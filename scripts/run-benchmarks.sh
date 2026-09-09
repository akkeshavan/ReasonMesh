#!/usr/bin/env bash
# run-benchmarks.sh — execute all three benchmark phases on the Hetzner fleet
#
# Prerequisites:
#   source scripts/env.sh      (written by provision.sh)
#
# Phases:
#   1  G2 scaling      single-node, 1–32 workers, isolated vs AKX selective
#                      Machine: rm-bench (CCX53, 32 vCPU)
#                      ~45 min
#
#   2  G3 vs baselines ReasonMesh 16w-selective vs Z3 / CaDiCaL / Kissat
#                      Machine: rm-bench (CCX53)
#                      ~60 min (21 problems × 4 solvers × up to 300s)
#
#   3  G4 distributed  4-node TCP AKX sharing vs single-node 16w baseline
#                      Machines: rm-node1..4 (CCX23, 8 vCPU each)
#                      ~30 min (5 problems × 2 configs)
#
# Results land on rm-bench at /opt/reasonmesh/local/results/.
# Run collect.sh afterwards to pull them to experiments/data/.
#
# Usage:
#   source scripts/env.sh
#   ./scripts/run-benchmarks.sh [--phase 1|2|3]   # run one phase only
#   ./scripts/run-benchmarks.sh                    # run all three

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# ── Load environment ───────────────────────────────────────────────────────────
ENV_FILE="$SCRIPT_DIR/env.sh"
[[ -f "$ENV_FILE" ]] || { echo "error: scripts/env.sh not found — run provision.sh first" >&2; exit 1; }
# shellcheck disable=SC1090
source "$ENV_FILE"

for v in RM_SSH_KEY RM_BENCH_IP RM_NODE1_IP RM_NODE2_IP RM_NODE3_IP RM_NODE4_IP \
          RM_NODE1_PRIV RM_NODE2_PRIV RM_NODE3_PRIV RM_NODE4_PRIV; do
  [[ -n "${!v:-}" ]] || { echo "error: $v not set in env.sh" >&2; exit 1; }
done

# ── Argument parsing ───────────────────────────────────────────────────────────
RUN_PHASES=(1 2 3)
if [[ "${1:-}" == "--phase" && -n "${2:-}" ]]; then
  RUN_PHASES=("$2")
fi

# ── Helpers ───────────────────────────────────────────────────────────────────
GREEN='\033[0;32m'; YELLOW='\033[1;33m'; RED='\033[0;31m'; CYAN='\033[0;36m'; NC='\033[0m'
REMOTE_LOG="/tmp/reasonmesh-bench.log"
ts()     { date +%H:%M:%S; }
log()    { echo -e "${GREEN}[$(ts) bench]${NC} $*"; }
step()   { echo -e "${CYAN}[$(ts)] · $*${NC}"; }
phase()  { echo -e "\n${CYAN}══════════════════════════════════════════════${NC}"; \
           echo -e "${CYAN}  [$(ts)]  $*${NC}"; \
           echo -e "${CYAN}══════════════════════════════════════════════${NC}"; }
warn()   { echo -e "${YELLOW}[$(ts) warn]${NC} $*" >&2; }
die()    { echo -e "${RED}[$(ts) error]${NC} $*" >&2; exit 1; }

# SSH option array — immune to IFS and word-splitting issues.
# Never use a string variable for SSH options; always use "${SSH_ARGS[@]}".
SSH_ARGS=(-i "$RM_SSH_KEY"
          -o StrictHostKeyChecking=no
          -o UserKnownHostsFile=/dev/null
          -o LogLevel=ERROR
          -o ServerAliveInterval=15
          -o ServerAliveCountMax=8
          -o ConnectTimeout=20)
ssh_bench() { ssh "${SSH_ARGS[@]}" "root@$RM_BENCH_IP" "$@"; }
ssh_node()  {
  local n=$1; shift
  local ip_var="RM_NODE${n}_IP"
  ssh "${SSH_ARGS[@]}" "root@${!ip_var}" "$@"
}

# Write a timestamped line to the running log on rm-bench (best-effort)
rlog() { ssh_bench "echo '[$(ts)] $*' >> $REMOTE_LOG" 2>/dev/null || true; }

# Run a manifest on rm-bench; save JSON to the given remote path.
# Skips if the result file already exists (idempotent).
run_manifest() {
  local manifest=$1          # relative to /opt/reasonmesh/local/
  local result_path=$2       # absolute path on rm-bench
  local label=${3:-$manifest}

  if ssh_bench "test -s '$result_path' && grep -q 'outcome' '$result_path'" 2>/dev/null; then
    log "  SKIP $label (result exists)"
    rlog "SKIP $label"
    return 0
  fi

  step "RUN $label  [$(ts)]"
  rlog "START $label"
  local start=$SECONDS
  # Run nohup'd so the benchmark process survives any transient SSH disconnect.
  local done_marker="/tmp/.bench-done-${manifest//[\/.]/_}"
  ssh_bench "rm -f '$done_marker'; \
    nohup bash -c 'mkdir -p \$(dirname \"$result_path\") && \
      cd /opt/reasonmesh/local && \
      reasonmesh benchmark $manifest > \"$result_path\" 2>/tmp/bench-stderr.txt; \
      echo done > \"$done_marker\"' &>/dev/null &"
  # Poll until done marker appears; log progress every 30s
  local poll=0
  while ! ssh_bench "test -f '$done_marker'" 2>/dev/null; do
    sleep 30; poll=$((poll + 30))
    step "  ... $label running  ${poll}s elapsed"
    rlog "  ... $label running ${poll}s"
  done
  local elapsed=$((SECONDS - start))

  if ssh_bench "grep -q 'outcome' '$result_path'" 2>/dev/null; then
    local par2
    par2=$(ssh_bench "python3 -c \
      \"import json,sys; d=json.load(open('$result_path')); \
        print(f\\\"par2={d['summary']['par2_ns']/1e9:.1f}s  solved={d['summary']['solved']}/{len(d['problems'])}\\\")\""
    ) 2>/dev/null || par2=""
    log "  DONE $label  elapsed=${elapsed}s  $par2"
    rlog "DONE $label elapsed=${elapsed}s $par2"
  else
    warn "  FAIL $label — check /tmp/bench-stderr.txt on rm-bench"
    rlog "FAIL $label elapsed=${elapsed}s"
  fi
}

# Like run_manifest but runs one problem at a time via run-per-problem.py,
# writing a JSONL progress line to <result>.progress.jsonl after each problem.
run_manifest_with_progress() {
  local manifest=$1
  local result_path=$2
  local label=${3:-$manifest}
  local progress_path="${result_path%.json}.progress.jsonl"

  if ssh_bench "test -f '$result_path' && grep -q 'outcome' '$result_path'" 2>/dev/null; then
    log "  SKIP $label (result exists)"
    rlog "SKIP $label"
    return 0
  fi

  local n_done=0
  if ssh_bench "test -s '$progress_path'" 2>/dev/null; then
    n_done=$(ssh_bench "wc -l < '$progress_path'" 2>/dev/null || echo 0)
    step "RESUME $label  ($n_done problems already done)  [$(ts)]"
    rlog "RESUME $label n_done=$n_done"
  else
    step "RUN $label  [$(ts)]"
    rlog "START $label"
  fi

  local start=$SECONDS
  ssh_bench "mkdir -p \$(dirname '$result_path') && \
    cd /opt/reasonmesh/local && \
    python3 run-per-problem.py '$manifest' '$result_path' '$progress_path'" \
    | while IFS= read -r line; do
        log "    $line"
        # mirror each problem completion to the remote log
        echo "$line" | grep -q '"outcome"' && rlog "  problem done: $line" || true
      done
  local elapsed=$((SECONDS - start))
  log "  DONE $label  elapsed=${elapsed}s"
  rlog "DONE $label elapsed=${elapsed}s"
}

# ── 0. Init remote log + sync ─────────────────────────────────────────────────
step "0/3  Init remote log on rm-bench"
ssh_bench "echo '=== ReasonMesh benchmark run started at $(date -u +%Y-%m-%dT%H:%M:%SZ) ===' > $REMOTE_LOG"
log "Remote progress log: ssh root@$RM_BENCH_IP 'tail -f $REMOTE_LOG'"

# rsync_cmd wraps rsync with the same SSH options as ssh_bench/ssh_node.
# -e must receive the full "ssh <opts>" as a single quoted argument — do not
# expand $SSH_COMMON into separate words or rsync treats them as its own flags.
rsync_cmd() { rsync -az -e "ssh ${SSH_ARGS[*]}" "$@"; }

step "0/3  Sync experiments/ + benchmarks/ → rm-bench  [$(ts)]"
# Manifests and scripts go to local/ (cwd for benchmark runs).
# Benchmarks (CNF files) go to benchmarks/ so that manifest-relative paths
# "../benchmarks/g1/foo.cnf" resolve correctly from local/.
rsync_cmd \
  --exclude 'results/' \
  --exclude 'data/' \
  "$REPO_ROOT/experiments/" \
  "$REPO_ROOT/scripts/run-per-problem.py" \
  "root@$RM_BENCH_IP:/opt/reasonmesh/local/"
rsync_cmd \
  "$REPO_ROOT/benchmarks/" \
  "root@$RM_BENCH_IP:/opt/reasonmesh/benchmarks/"
log "  rm-bench sync done"
rlog "sync rm-bench done"

step "0/3  Sync benchmarks/ → rm-node1..4 (parallel)  [$(ts)]"
for n in 1 2 3 4; do
  ip_var="RM_NODE${n}_IP"
  rsync_cmd \
    "$REPO_ROOT/benchmarks/" \
    "root@${!ip_var}:/opt/reasonmesh/benchmarks/" &
done
wait
log "  node sync done"
rlog "sync nodes done"

RESULTS_BASE="/opt/reasonmesh/local/results"

# ── Phase 1: G2 scaling study ─────────────────────────────────────────────────
if printf '%s\n' "${RUN_PHASES[@]}" | grep -q '^1$'; then
phase "Phase 1 — G2 scaling study (1–32 workers, isolated vs AKX selective)"
log "Machine: rm-bench cpx62 (16 shared vCPU)"
log "Expected duration: ~45 minutes"
rlog "=== PHASE 1 G2 START ==="

G2_MANIFESTS=(
  "g2-scaling-1w.toml"
  "g2-scaling-2w-isolated.toml"
  "g2-scaling-2w-selective.toml"
  "g2-scaling-4w-isolated.toml"
  "g2-scaling-4w-selective.toml"
  "g2-scaling-8w-isolated.toml"
  "g2-scaling-8w-selective.toml"
  "g2-scaling-16w-isolated.toml"
  "g2-scaling-16w-selective.toml"
  # 32w manifests omitted: require cpx82+ (32 shared vCPU); re-add if a larger instance is provisioned
)

for manifest in "${G2_MANIFESTS[@]}"; do
  name="${manifest%.toml}"
  run_manifest "$manifest" "$RESULTS_BASE/g2/${name}.json" "$name"
done

log "Phase 1 complete"
rlog "=== PHASE 1 G2 DONE ==="
fi

# ── Phase 2: G3 vs baselines ──────────────────────────────────────────────────
if printf '%s\n' "${RUN_PHASES[@]}" | grep -q '^2$'; then
phase "Phase 2 — G3 vs baselines (ReasonMesh 16w vs Z3 / CaDiCaL / Kissat)"
log "Machine: rm-bench cpx62 (16 shared vCPU)"
log "Expected duration: ~60 minutes (21 problems × 4 solvers × 300s max)"
rlog "=== PHASE 2 G3 START ==="

run_manifest_with_progress "g3-vs-all-baselines.toml" \
  "$RESULTS_BASE/g3/g3-vs-all-baselines.json" \
  "g3-vs-all-baselines"

log "Phase 2 complete"
rlog "=== PHASE 2 G3 DONE ==="
fi

# ── Phase 3: G4 distributed experiment ────────────────────────────────────────
if printf '%s\n' "${RUN_PHASES[@]}" | grep -q '^3$'; then
phase "Phase 3 — G4 distributed (4-node TCP AKX vs single-node 16w)"
log "Machines: rm-bench (baseline) + rm-node1..4 cpx32 (distributed)"
log "Expected duration: ~30 minutes"
rlog "=== PHASE 3 G4 START ==="

BENCH_DATA_DIR="/opt/reasonmesh/benchmarks"   # paths on rm-bench (matches ../benchmarks/ in manifests)
NODE_DATA_DIR="/opt/reasonmesh/benchmarks" # paths on rm-node1..4
RESULTS_G4="$RESULTS_BASE/g4"
ssh_bench "mkdir -p '$RESULTS_G4'"

# Problems for the distributed experiment.
# Format: "name|bench_path|node_path"
# bench_path — used by run_single_node_baseline (runs on rm-bench)
# node_path  — used by run_distributed (runs on rm-node1..4)
# Only include problems ReasonMesh can actually solve within the timeout
# (php-9-8, php-10-9, r3sat-238-x, r3sat-242-1 all solved in G3).
G4_PROBLEMS=(
  "php-9-8|$BENCH_DATA_DIR/g1/php-9-8.cnf|$NODE_DATA_DIR/g1/php-9-8.cnf"
  "php-10-9|$BENCH_DATA_DIR/g1/php-10-9.cnf|$NODE_DATA_DIR/g1/php-10-9.cnf"
  "r3sat-238-1|$BENCH_DATA_DIR/g2/r3sat-238-1.cnf|$NODE_DATA_DIR/g2/r3sat-238-1.cnf"
  "r3sat-238-2|$BENCH_DATA_DIR/g2/r3sat-238-2.cnf|$NODE_DATA_DIR/g2/r3sat-238-2.cnf"
  "r3sat-242-1|$BENCH_DATA_DIR/g2/r3sat-242-1.cnf|$NODE_DATA_DIR/g2/r3sat-242-1.cnf"
)

TIMEOUT_SECS=180  # 3 min per problem per config

# ─── Helper: run single-node baseline on rm-bench ─────────────────────────────
# Writes verdict + wall_ms to /tmp/g4-sn-out.txt on rm-bench (nohup'd),
# then polls every 10s. Returns two lines to stdout: verdict, wall_ms.
run_single_node_baseline() {
  local problem_path=$1 workers=${2:-16} seed=${3:-1}
  local out="/tmp/g4-sn-out.txt" done_marker="/tmp/g4-sn-done"
  ssh_bench "rm -f '$out' '$done_marker'; \
    nohup bash -c '\
      start=\$(date +%s%N); \
      verdict=\$(timeout $((TIMEOUT_SECS + 5)) \
        reasonmesh solve \"$problem_path\" --workers $workers --seed $seed \
          2>/dev/null | grep -m1 \"^s \" || echo \"s UNKNOWN\"); \
      end=\$(date +%s%N); \
      wall_ms=\$(( (end - start) / 1000000 )); \
      echo \"\$verdict\" > \"$out\"; echo \"\$wall_ms\" >> \"$out\"; \
      touch \"$done_marker\"' &>/dev/null &"
  local poll=0
  while ! ssh_bench "test -f '$done_marker'" 2>/dev/null; do
    sleep 10; poll=$((poll+10))
    [[ $((poll % 30)) -eq 0 ]] && { step "  ... single-node baseline running ${poll}s"; rlog "  sn running ${poll}s"; }
  done
  ssh_bench "cat '$out'" 2>/dev/null || { echo "s UNKNOWN"; echo "0"; }
}

# ─── Helper: run 4-node distributed solve ─────────────────────────────────────
# All 4 nodes solve the same problem with 4 workers each (16 total across the fleet).
# Seeds are staggered so each node explores a different heuristic trajectory.
# Returns the verdict and wall time (time to first verdict across any node).
run_distributed() {
  local problem_path=$1  # path to the CNF on each node (must already be there)
  local port=9000

  # Private IPs of the 4 nodes
  local priv1="$RM_NODE1_PRIV"
  local priv2="$RM_NODE2_PRIV"
  local priv3="$RM_NODE3_PRIV"
  local priv4="$RM_NODE4_PRIV"

  # Peer lists for each node (exclude self)
  local peers1="--peer $priv2:$port --peer $priv3:$port --peer $priv4:$port"
  local peers2="--peer $priv1:$port --peer $priv3:$port --peer $priv4:$port"
  local peers3="--peer $priv1:$port --peer $priv2:$port --peer $priv4:$port"
  local peers4="--peer $priv1:$port --peer $priv2:$port --peer $priv3:$port"

  # Result and PID files on each node
  local res_file="/tmp/rm-g4-result.txt"
  local pid_file="/tmp/rm-g4.pid"

  # Clear previous results on all nodes
  for n in 1 2 3 4; do
    ssh_node $n "rm -f $res_file $pid_file" 2>/dev/null &
  done
  wait

  # Start all 4 nodes in background (SSH -n = no stdin; nohup keeps it alive)
  local node_cmds=(
    "nohup reasonmesh serve '$problem_path' --port $port --workers 4 --seed 1 $peers1 --timeout-secs $TIMEOUT_SECS > $res_file 2>&1 & echo \$! > $pid_file"
    "nohup reasonmesh serve '$problem_path' --port $port --workers 4 --seed 5 $peers2 --timeout-secs $TIMEOUT_SECS > $res_file 2>&1 & echo \$! > $pid_file"
    "nohup reasonmesh serve '$problem_path' --port $port --workers 4 --seed 9 $peers3 --timeout-secs $TIMEOUT_SECS > $res_file 2>&1 & echo \$! > $pid_file"
    "nohup reasonmesh serve '$problem_path' --port $port --workers 4 --seed 13 $peers4 --timeout-secs $TIMEOUT_SECS > $res_file 2>&1 & echo \$! > $pid_file"
  )

  local start_ms
  start_ms=$(date +%s%N)
  start_ms=$((start_ms / 1000000))

  for n in 1 2 3 4; do
    local ip_var="RM_NODE${n}_IP"
    ssh "${SSH_ARGS[@]}" \
      -n "root@${!ip_var}" \
      "${node_cmds[$((n-1))]}" &
  done

  # Small grace period for all nodes to bind their ports before peers connect
  sleep 3

  # Poll all nodes until any reports a verdict; log every 30s
  local verdict="s UNKNOWN"
  local found=0
  local elapsed_ms=0
  local last_log_ms=0
  local poll_interval=10  # seconds

  while [[ $found -eq 0 ]]; do
    sleep $poll_interval
    now_ms=$(date +%s%N); now_ms=$((now_ms / 1000000))
    elapsed_ms=$((now_ms - start_ms))

    for n in 1 2 3 4; do
      local v
      v=$(ssh_node $n "grep -m1 '^s ' $res_file 2>/dev/null" 2>/dev/null || true)
      if [[ -n "$v" ]]; then
        verdict="$v"; found=1; break
      fi
    done

    if [[ $found -eq 0 && $((elapsed_ms - last_log_ms)) -ge 30000 ]]; then
      local elapsed_s=$((elapsed_ms / 1000))
      step "  ... distributed solving  ${elapsed_s}s / ${TIMEOUT_SECS}s"
      rlog "  distributed running ${elapsed_s}s"
      last_log_ms=$elapsed_ms
    fi

    if [[ $found -eq 0 && $elapsed_ms -ge $((TIMEOUT_SECS * 1000)) ]]; then
      warn "  Distributed run timed out after ${TIMEOUT_SECS}s"
      break
    fi
  done

  # Kill all remote solver processes
  for n in 1 2 3 4; do
    ssh_node $n "kill \$(cat $pid_file 2>/dev/null) 2>/dev/null; pkill -f 'reasonmesh serve' 2>/dev/null" &
  done
  wait

  echo "$verdict"
  echo "$elapsed_ms"
}

# ─── Run G4 experiments ────────────────────────────────────────────────────────
G4_RESULT_FILE="$RESULTS_G4/g4-distributed.json"
G4_PROGRESS_FILE="$RESULTS_G4/g4-distributed.progress.jsonl"

if ssh_bench "test -s '$G4_RESULT_FILE' && python3 -c \"import json; json.load(open('$G4_RESULT_FILE'))\" 2>/dev/null"; then
  log "SKIP G4 (result exists at $G4_RESULT_FILE)"
else

# Start building the JSON result on the local side; we'll write it to rm-bench at the end
G4_JSON='{"schema_version":1,"experiment":"g4-distributed","description":"4-node AKX TCP sharing vs single-node 16w baseline",'
G4_JSON+="\"timeout_secs\":$TIMEOUT_SECS,"
G4_JSON+='"problems":['
FIRST_PROBLEM=1

# Load already-completed problems from progress JSONL (for resumption).
# G4_DONE_LIST is a space-separated string of completed problem names —
# avoids declare -A which requires Bash 4+ (macOS ships Bash 3.2).
G4_DONE_LIST=""
if ssh_bench "test -s '$G4_PROGRESS_FILE'" 2>/dev/null; then
  log "  Found existing G4 progress — resuming"
  while IFS= read -r line; do
    pname=$(echo "$line" | python3 -c "import json,sys; print(json.load(sys.stdin)['name'])" 2>/dev/null) || continue
    [[ -z "$pname" ]] && continue
    G4_DONE_LIST="$G4_DONE_LIST $pname"
    [[ $FIRST_PROBLEM -eq 0 ]] && G4_JSON+=','
    G4_JSON+="$line"
    FIRST_PROBLEM=0
    log "  SKIP $pname (already in progress JSONL)"
  done < <(ssh_bench "cat '$G4_PROGRESS_FILE'" 2>/dev/null)
fi

for entry in "${G4_PROBLEMS[@]}"; do
  prob_name="${entry%%|*}"
  rest="${entry#*|}"
  bench_path="${rest%%|*}"
  node_path="${rest##*|}"

  # Skip if this problem was already completed in a prior run
  if echo " $G4_DONE_LIST " | grep -q " $prob_name "; then
    continue
  fi

  log "G4: $prob_name"

  # ── Single-node baseline (rm-bench, 16 workers) ──────────────────────────
  log "  single-node 16w baseline on rm-bench…"
  single_output=$(run_single_node_baseline "$bench_path" 16 1) || true
  single_verdict=$(printf '%s' "$single_output" | head -n1)
  single_verdict="${single_verdict:-s UNKNOWN}"
  single_wall_ms=$(printf '%s' "$single_output" | sed -n '2p')
  single_wall_ms="${single_wall_ms:-0}"
  single_wall_s=$(python3 -c "print(round(${single_wall_ms}/1000,3))")
  log "    → $single_verdict  wall=${single_wall_s}s"

  # ── Distributed run (4 × cpx32, 4 workers each, AKX TCP sharing) ─────────
  log "  distributed 4-node×4w on rm-node1..4…"
  dist_output=$(run_distributed "$node_path") || true
  dist_verdict=$(printf '%s' "$dist_output" | head -n1)
  dist_verdict="${dist_verdict:-s UNKNOWN}"
  dist_wall_ms=$(printf '%s' "$dist_output" | sed -n '2p')
  dist_wall_ms="${dist_wall_ms:-0}"
  dist_wall_s=$(python3 -c "print(round(${dist_wall_ms}/1000,3))")
  log "    → $dist_verdict  wall=${dist_wall_s}s"

  # ── Speedup vs baseline ────────────────────────────────────────────────────
  speedup="null"
  if [[ "$single_verdict" != "s UNKNOWN" && "$dist_verdict" != "s UNKNOWN" \
        && "$single_wall_ms" -gt 0 && "$dist_wall_ms" -gt 0 ]]; then
    speedup=$(python3 -c "print(round($single_wall_ms/$dist_wall_ms,3))")
    log "    speedup: ${speedup}×"
  fi

  prob_json="{\"name\":\"$prob_name\","
  prob_json+="\"single_node\":{\"workers\":16,\"verdict\":\"$single_verdict\",\"wall_secs\":$single_wall_s,\"wall_ms\":$single_wall_ms},"
  prob_json+="\"distributed\":{\"nodes\":4,\"workers_per_node\":4,\"total_workers\":16,\"verdict\":\"$dist_verdict\",\"wall_secs\":$dist_wall_s,\"wall_ms\":$dist_wall_ms},"
  prob_json+="\"speedup\":$speedup}"

  [[ $FIRST_PROBLEM -eq 0 ]] && G4_JSON+=','
  G4_JSON+="$prob_json"
  FIRST_PROBLEM=0

  # Write one progress line per problem — retry up to 3× on SSH jitter
  attempts=0
  until echo "$prob_json" | ssh_bench "cat >> '$G4_PROGRESS_FILE'" 2>/dev/null; do
    attempts=$((attempts + 1))
    [[ $attempts -ge 3 ]] && { warn "Could not write G4 progress for $prob_name after 3 attempts"; break; }
    sleep 5
  done
  rlog "G4 $prob_name done sn=$single_verdict dist=$dist_verdict speedup=$speedup"
done

G4_JSON+=']}'

# Write final JSON to rm-bench — build it remotely to avoid pipe truncation
echo "$G4_JSON" | python3 -m json.tool > "/tmp/g4-result-local.json"
attempts=0
until ssh_bench "cat > '$G4_RESULT_FILE'" < "/tmp/g4-result-local.json" 2>/dev/null; do
  attempts=$((attempts + 1))
  [[ $attempts -ge 3 ]] && { warn "Could not write G4 result file after 3 attempts"; break; }
  sleep 5
done
rm -f "/tmp/g4-result-local.json"

log "G4 result written to $G4_RESULT_FILE"
rlog "G4 DONE result written"
fi  # end skip check

log "Phase 3 complete"
rlog "=== PHASE 3 G4 DONE ==="
fi

# ── Summary ───────────────────────────────────────────────────────────────────
phase "All requested phases complete"
log "Results on rm-bench at /opt/reasonmesh/local/results/"
log ""
log "Run analysis locally:"
log "  ./scripts/collect.sh               # pull results to experiments/data/"
log "  python3 experiments/analyze_g2.py  # G2 scaling table + PAR-2 curve"
log "  python3 experiments/analyze_g3.py  # G3 vs-baseline comparison"
log "  python3 experiments/analyze_g4.py  # G4 distributed speedup table"
