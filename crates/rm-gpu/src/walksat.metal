#include <metal_stdlib>
using namespace metal;

// Must match WalkParams in metal_backend.rs byte-for-byte.
struct WalkParams {
    uint  num_vars;
    uint  num_clauses;
    uint  max_clause_len;
    uint  steps;
    ulong seed;
    uint  noise_pct;   // e.g. 15 = 15 % noise
    uint  _pad;
};

// Literal raw-index encoding (same as rm-akx Literal):
//   positive literal for variable v: raw = v * 2
//   negative literal for variable v: raw = v * 2 + 1

kernel void walksat(
    device const int*       clause_lits  [[ buffer(0) ]],  // flat, padded rows [ci * mcl + k]
    device const uint*      clause_len   [[ buffer(1) ]],  // length of clause ci
    device const uint*      occ_data     [[ buffer(2) ]],  // concatenated occurrence lists
    device const uint*      occ_start    [[ buffer(3) ]],  // start in occ_data for lit_raw
    device const uint*      occ_count    [[ buffer(4) ]],  // number of entries for lit_raw
    device uint8_t*         assign       [[ buffer(5) ]],  // [tid * (nv+1) + var]
    device uint8_t*         clause_sat   [[ buffer(6) ]],  // [tid * nc + ci]
    device uint2*           out          [[ buffer(7) ]],  // (best_sat_count, tid) per thread
    device const WalkParams* params      [[ buffer(8) ]],
    uint tid [[ thread_position_in_grid ]]
) {
    const uint nv    = params->num_vars;
    const uint nc    = params->num_clauses;
    const uint mcl   = params->max_clause_len;
    const uint steps = params->steps;

    // Guard against extra threads in the last threadgroup.
    // num_trajectories is embedded in the dispatch size; threads beyond
    // it have nothing to do.  We use nc == 0 as a proxy for "no work"
    // — the host never launches this kernel with nc == 0 — so just
    // guard on the out-of-bounds trajectory case via the dispatch shape.
    // (The host ensures dispatch size == num_trajectories exactly.)

    device uint8_t* my_assign = assign    + (ulong)tid * (nv + 1);
    device uint8_t* my_sat    = clause_sat + (ulong)tid * nc;

    // Per-thread RNG (xorshift-mix of seed and tid).
    ulong rng = params->seed ^ ((ulong)tid * 2654435761UL);
    rng ^= rng >> 33;
    rng *= 0xff51afd7ed558ccdUL;
    rng ^= rng >> 33;

    // Initialise assignment randomly.
    for (uint v = 1; v <= nv; v++) {
        rng = rng * 6364136223846793005UL + 1442695040888963407UL;
        my_assign[v] = (uint8_t)((rng >> 33) & 1);
    }

    // Compute initial clause-satisfaction counts.
    uint total_sat = 0;
    for (uint ci = 0; ci < nc; ci++) {
        uint len = clause_len[ci];
        uint s = 0;
        for (uint k = 0; k < len; k++) {
            int  lit = clause_lits[ci * mcl + k];
            uint var = (uint)(lit < 0 ? -lit : lit);
            uint8_t want = (lit > 0) ? 1u : 0u;
            if (my_assign[var] == want) s++;
        }
        uint8_t sat = (uint8_t)min(s, 255u);
        my_sat[ci] = sat;
        if (sat > 0) total_sat++;
    }

    uint best_sat = total_sat;

    // Main WalkSAT loop.
    for (uint step = 0; step < steps; step++) {
        if (total_sat >= nc) break;

        // Pick a random unsatisfied clause (retry once if we land on a satisfied one).
        rng = rng * 6364136223846793005UL + 1442695040888963407UL;
        uint pick = (uint)((rng >> 33) % nc);
        if (my_sat[pick] > 0) {
            rng = rng * 6364136223846793005UL + 1442695040888963407UL;
            pick = (uint)((rng >> 33) % nc);
            if (my_sat[pick] > 0) continue;
        }

        uint len = clause_len[pick];
        if (len == 0) continue;

        // Noise: with probability noise_pct% pick a random literal.
        rng = rng * 6364136223846793005UL + 1442695040888963407UL;
        bool noise = ((rng >> 33) % 100) < params->noise_pct;

        uint flip_var = 0;
        if (noise) {
            rng = rng * 6364136223846793005UL + 1442695040888963407UL;
            uint ki = (uint)((rng >> 33) % len);
            int lit = clause_lits[pick * mcl + ki];
            flip_var = (uint)(lit < 0 ? -lit : lit);
        } else {
            // Greedy: pick variable in clause with minimum break count.
            uint min_break = 0xFFFFFFFFu;
            for (uint k = 0; k < len; k++) {
                int  lit = clause_lits[pick * mcl + k];
                uint var = (uint)(lit < 0 ? -lit : lit);
                if (var == 0 || var > nv) continue;
                // Raw index of the literal that is currently TRUE for this var.
                uint cur_raw = var * 2 + (my_assign[var] ? 0u : 1u);
                uint oc  = occ_count[cur_raw];
                uint os  = occ_start[cur_raw];
                uint brk = 0;
                for (uint j = 0; j < oc; j++) {
                    if (my_sat[occ_data[os + j]] == 1) brk++;
                }
                if (brk < min_break) {
                    min_break = brk;
                    flip_var  = var;
                    if (brk == 0) break;
                }
            }
        }

        if (flip_var == 0 || flip_var > nv) continue;

        // Perform flip.
        uint8_t new_val = my_assign[flip_var] ^ 1u;
        my_assign[flip_var] = new_val;

        // old literal (what it WAS before flip): opposite sign of new_val
        uint old_raw = flip_var * 2 + (new_val ? 1u : 0u);
        // new literal: same sign as new_val
        uint new_raw = flip_var * 2 + (new_val ? 0u : 1u);

        // Clauses containing the old literal lose a satisfied literal.
        {
            uint oc = occ_count[old_raw];
            uint os = occ_start[old_raw];
            for (uint j = 0; j < oc; j++) {
                uint ci = occ_data[os + j];
                if (my_sat[ci] == 1) total_sat--;
                if (my_sat[ci] > 0) my_sat[ci]--;
            }
        }
        // Clauses containing the new literal gain a satisfied literal.
        {
            uint oc = occ_count[new_raw];
            uint os = occ_start[new_raw];
            for (uint j = 0; j < oc; j++) {
                uint ci = occ_data[os + j];
                if (my_sat[ci] == 0) total_sat++;
                if (my_sat[ci] < 255u) my_sat[ci]++;
            }
        }

        if (total_sat > best_sat) best_sat = total_sat;
    }

    out[tid] = uint2(best_sat, tid);
}
