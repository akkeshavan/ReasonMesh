//! Metal backend — WalkSAT kernel on Apple Silicon unified memory.

use crate::{GpuAccelerator, GpuClause, WalkResult, build_occurrence_lists};
use metal::{
    Device, MTLResourceOptions, MTLSize,
};
use std::ffi::c_void;

// Must match `WalkParams` in walksat.metal byte-for-byte.
#[repr(C)]
struct WalkParams {
    num_vars:       u32,
    num_clauses:    u32,
    max_clause_len: u32,
    steps:          u32,
    seed:           u64,
    noise_pct:      u32,
    /// Percentage of variables to randomly flip from initial_polarity when
    /// seeding each trajectory (0 = start exactly from CDCL phase; 20 = 20%
    /// of variables flipped, exploring near the current phase rather than
    /// replacing it with a random assignment).
    init_noise_pct: u32,
}

pub struct MetalAccelerator {
    device:           Device,
    queue:            metal::CommandQueue,
    pipeline_walk:    metal::ComputePipelineState,
    device_name_str:  String,
}

impl MetalAccelerator {
    pub fn new() -> Result<Self, String> {
        let device = Device::system_default().ok_or("No Metal device found")?;
        let queue = device.new_command_queue();

        let src = include_str!("walksat.metal");
        let opts = metal::CompileOptions::new();
        let library = device
            .new_library_with_source(src, &opts)
            .map_err(|e| format!("MSL compile error: {e}"))?;
        let func = library
            .get_function("walksat", None)
            .map_err(|e| format!("function not found: {e}"))?;
        let pipeline_walk = device
            .new_compute_pipeline_state_with_function(&func)
            .map_err(|e| format!("pipeline error: {e}"))?;

        let device_name_str = device.name().to_string();
        Ok(Self {
            device,
            queue,
            pipeline_walk,
            device_name_str,
        })
    }
}

// ---------------------------------------------------------------------------
// Buffer helpers
// ---------------------------------------------------------------------------

fn make_buffer<T: Sized>(device: &Device, data: &[T]) -> metal::Buffer {
    let byte_len = (data.len() * std::mem::size_of::<T>()) as u64;
    device.new_buffer_with_data(
        data.as_ptr() as *const c_void,
        byte_len,
        MTLResourceOptions::StorageModeShared,
    )
}

fn make_buffer_zeroed(device: &Device, bytes: usize) -> metal::Buffer {
    device.new_buffer(bytes as u64, MTLResourceOptions::StorageModeShared)
}

// ---------------------------------------------------------------------------
// GpuAccelerator implementation
// ---------------------------------------------------------------------------

impl GpuAccelerator for MetalAccelerator {
    fn walk(
        &self,
        clauses: &[GpuClause],
        num_vars: u32,
        initial_polarity: &[bool],
        seed: u64,
        num_trajectories: u32,
        steps_per_var: u32,
    ) -> WalkResult {
        let nc = clauses.len() as u32;
        let nv = num_vars;
        let traj = num_trajectories as usize;

        if nc == 0 || nv == 0 || traj == 0 {
            return WalkResult {
                polarity: vec![false; nv as usize + 1],
                sat_count: 0,
            };
        }

        // ---- Build flat clause literal buffer (padded rows) ----
        let max_clause_len = clauses
            .iter()
            .map(|c| c.lits.len())
            .max()
            .unwrap_or(1)
            .max(1) as u32;

        let mut flat_lits: Vec<i32> = vec![0i32; (nc * max_clause_len) as usize];
        let mut flat_len:  Vec<u32> = Vec::with_capacity(nc as usize);
        for (ci, c) in clauses.iter().enumerate() {
            let row = ci * max_clause_len as usize;
            for (k, &lit) in c.lits.iter().enumerate() {
                flat_lits[row + k] = lit;
            }
            flat_len.push(c.lits.len() as u32);
        }

        // ---- Build occurrence lists ----
        let occ = build_occurrence_lists(clauses, num_vars);
        let occ_cap = occ.len(); // (nv + 1) * 2
        let mut occ_data_vec:  Vec<u32> = Vec::new();
        let mut occ_start_vec: Vec<u32> = vec![0u32; occ_cap];
        let mut occ_count_vec: Vec<u32> = vec![0u32; occ_cap];
        for (raw, list) in occ.iter().enumerate() {
            occ_start_vec[raw] = occ_data_vec.len() as u32;
            occ_count_vec[raw] = list.len() as u32;
            occ_data_vec.extend_from_slice(list);
        }
        if occ_data_vec.is_empty() {
            occ_data_vec.push(0); // Metal forbids zero-length buffers
        }

        // ---- Initial polarity buffer (CDCL phase hint, index 0 unused) ----
        let init_pol_u8: Vec<u8> = (0..=nv as usize)
            .map(|v| if v < initial_polarity.len() && initial_polarity[v] { 1u8 } else { 0u8 })
            .collect();

        // ---- Per-thread data sizes ----
        let assign_bytes = traj * (nv as usize + 1);
        let sat_bytes    = traj * nc as usize;
        let out_bytes    = traj * 2 * 4; // traj × uint2 × 4 bytes each field

        // ---- Steps ----
        let steps = nv.saturating_mul(steps_per_var).max(1);

        // ---- Params ----
        let params = WalkParams {
            num_vars:       nv,
            num_clauses:    nc,
            max_clause_len,
            steps,
            seed,
            noise_pct:      15,
            // 20% of variables flipped from the CDCL phase per trajectory.
            // Trajectories start near the current phase and explore outward —
            // WalkSAT refines rather than replaces the solver's polarity table.
            init_noise_pct: 20,
        };

        // ---- Allocate buffers (all StorageModeShared for zero-copy) ----
        let buf_clause_lits   = make_buffer(&self.device, &flat_lits);
        let buf_clause_len    = make_buffer(&self.device, &flat_len);
        let buf_occ_data      = make_buffer(&self.device, &occ_data_vec);
        let buf_occ_start     = make_buffer(&self.device, &occ_start_vec);
        let buf_occ_count     = make_buffer(&self.device, &occ_count_vec);
        let buf_assign        = make_buffer_zeroed(&self.device, assign_bytes);
        let buf_clause_sat    = make_buffer_zeroed(&self.device, sat_bytes);
        let buf_out           = make_buffer_zeroed(&self.device, out_bytes);
        let buf_params        = make_buffer(&self.device, std::slice::from_ref(&params));
        let buf_init_polarity = make_buffer(&self.device, &init_pol_u8);

        // ---- Encode and dispatch ----
        let cmd_buf = self.queue.new_command_buffer();
        let encoder = cmd_buf.new_compute_command_encoder();
        encoder.set_compute_pipeline_state(&self.pipeline_walk);
        encoder.set_buffer(0, Some(&buf_clause_lits),   0);
        encoder.set_buffer(1, Some(&buf_clause_len),    0);
        encoder.set_buffer(2, Some(&buf_occ_data),      0);
        encoder.set_buffer(3, Some(&buf_occ_start),     0);
        encoder.set_buffer(4, Some(&buf_occ_count),     0);
        encoder.set_buffer(5, Some(&buf_assign),        0);
        encoder.set_buffer(6, Some(&buf_clause_sat),    0);
        encoder.set_buffer(7, Some(&buf_out),           0);
        encoder.set_buffer(8, Some(&buf_params),        0);
        encoder.set_buffer(9, Some(&buf_init_polarity), 0);

        let max_tg  = self.pipeline_walk.max_total_threads_per_threadgroup() as usize;
        let tg_size = max_tg.min(256).min(traj);

        // dispatch_threads dispatches exactly `traj` threads; Metal handles the
        // partial last threadgroup internally. Using dispatch_thread_groups would
        // launch ceil(traj/tg_size)*tg_size threads (up to tg_size-1 extras),
        // causing those threads to write beyond buf_assign / buf_out bounds.
        encoder.dispatch_threads(
            MTLSize { width: traj as u64, height: 1, depth: 1 },
            MTLSize { width: tg_size as u64, height: 1, depth: 1 },
        );
        encoder.end_encoding();
        cmd_buf.commit();
        cmd_buf.wait_until_completed();

        // ---- Read back: find thread with best sat count ----
        let out_slice: &[[u32; 2]] = unsafe {
            std::slice::from_raw_parts(buf_out.contents() as *const [u32; 2], traj)
        };

        let (best_sat, best_tid) = out_slice
            .iter()
            .map(|&[sat, tid]| (sat as usize, tid as usize))
            .max_by_key(|&(sat, _)| sat)
            .unwrap_or((0, 0));

        // Read assignment from the best thread.
        let assign_all: &[u8] = unsafe {
            std::slice::from_raw_parts(buf_assign.contents() as *const u8, assign_bytes)
        };
        let offset = best_tid * (nv as usize + 1);
        let best_assign = &assign_all[offset..offset + nv as usize + 1];

        let polarity: Vec<bool> = (0..=nv as usize)
            .map(|v| best_assign[v] != 0)
            .collect();

        WalkResult {
            polarity,
            sat_count: best_sat,
        }
    }

    fn device_name(&self) -> &str {
        &self.device_name_str
    }
}
