//! C FFI layer for direct Lean 4 (and C/C++) integration.
//!
//! All functions use a C-compatible ABI (`extern "C"`, `#[no_mangle]`).
//! Callers own heap-allocated objects and must call the corresponding
//! `rm_*_free` function to release them.
//!
//! # Result codes
//! Every `rm_solver_check` / `rm_solve_smtlib` / `rm_solve_batch` call returns:
//!   `0` = SAT, `1` = UNSAT, `2` = UNKNOWN
//!
//! # Lean 4 example
//! ```lean
//! def RmContext := USize
//! def RmSolver  := USize
//! def RmExpr    := USize
//! def RmModel   := USize
//!
//! @[extern "rm_context_new"]  opaque rmContextNew  (_ : Unit) : RmContext
//! @[extern "rm_context_free"] opaque rmContextFree (ctx : RmContext) : Unit
//! @[extern "rm_solver_new"]
//! opaque rmSolverNew (ctx : RmContext) (workers : UInt32) (budget : UInt64) : RmSolver
//! @[extern "rm_solver_assert"] opaque rmSolverAssert (s : RmSolver) (e : RmExpr) : Unit
//! @[extern "rm_solver_check"]
//! opaque rmSolverCheck (s : RmSolver) (modelOut : @& ByteArray) : Int32
//! @[extern "rm_solve_smtlib"]
//! opaque rmSolveSmtlib (text : @& String) (budget : UInt64) (modelOut : @& ByteArray) : Int32
//! ```

use crate::context::Context;
use crate::expr::Expr;
use crate::model::{Model, Value};
use crate::solve_smtlib_with_budget;
use crate::solver::{SatResult, Solver, SolverConfig};
use std::ffi::{c_char, CStr, CString};

// ---------------------------------------------------------------------------
// Result codes (mirrored in rm_api.h)
// ---------------------------------------------------------------------------

pub const RM_SAT: i32 = 0;
pub const RM_UNSAT: i32 = 1;
pub const RM_UNKNOWN: i32 = 2;

// ---------------------------------------------------------------------------
// Opaque C types — just thin newtype wrappers that go on the heap.
// The caller receives a raw `*mut Rm*` and owns the allocation.
// ---------------------------------------------------------------------------

pub struct RmContext(Context);
pub struct RmSolver(Solver);
pub struct RmExpr(Expr);
pub struct RmModel(Model);

// ---------------------------------------------------------------------------
// Context
// ---------------------------------------------------------------------------

#[no_mangle]
pub extern "C" fn rm_context_new() -> *mut RmContext {
    Box::into_raw(Box::new(RmContext(Context::new())))
}

/// # Safety
/// `ctx` must be a pointer returned by `rm_context_new` and not yet freed.
#[no_mangle]
pub unsafe extern "C" fn rm_context_free(ctx: *mut RmContext) {
    if !ctx.is_null() {
        drop(unsafe { Box::from_raw(ctx) });
    }
}

// ---------------------------------------------------------------------------
// Solver
// ---------------------------------------------------------------------------

/// Create a solver.  `num_workers` threads race on each `rm_solver_check`;
/// `max_conflicts` is the CDCL budget per thread (0 = unlimited).
///
/// # Safety
/// `ctx` must be a valid, non-null pointer returned by `rm_context_new`.
#[no_mangle]
pub unsafe extern "C" fn rm_solver_new(
    ctx: *const RmContext,
    num_workers: u32,
    max_conflicts: u64,
) -> *mut RmSolver {
    if ctx.is_null() {
        return std::ptr::null_mut();
    }
    let ctx_ref = unsafe { &(*ctx).0 };
    let cfg = SolverConfig {
        num_workers: num_workers.max(1) as usize,
        max_conflicts,
        timeout: None,
    };
    Box::into_raw(Box::new(RmSolver(Solver::with_config(ctx_ref, cfg))))
}

/// # Safety
/// `solver` must be a valid pointer returned by `rm_solver_new`.
#[no_mangle]
pub unsafe extern "C" fn rm_solver_free(solver: *mut RmSolver) {
    if !solver.is_null() {
        drop(unsafe { Box::from_raw(solver) });
    }
}

/// Assert an expression.  The solver clones the expression internally, so
/// the caller may call `rm_expr_free(expr)` immediately afterward.
///
/// # Safety
/// Both pointers must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_solver_assert(solver: *mut RmSolver, expr: *const RmExpr) {
    if solver.is_null() || expr.is_null() {
        return;
    }
    let s = unsafe { &mut (*solver).0 };
    let e = unsafe { &(*expr).0 };
    s.assert(e);
}

/// # Safety
/// `solver` must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_solver_push(solver: *mut RmSolver) {
    if !solver.is_null() {
        unsafe { (*solver).0.push() };
    }
}

/// # Safety
/// `solver` must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_solver_pop(solver: *mut RmSolver) {
    if !solver.is_null() {
        unsafe { (*solver).0.pop() };
    }
}

/// Check satisfiability.  Returns `RM_SAT` / `RM_UNSAT` / `RM_UNKNOWN`.
/// On `RM_SAT`, writes a heap-allocated model to `*model_out`; the caller
/// must free it with `rm_model_free`.  On other results `*model_out` is
/// set to null.
///
/// # Safety
/// `solver` must be valid and non-null.  `model_out` may be null (model
/// is then discarded on SAT).
#[no_mangle]
pub unsafe extern "C" fn rm_solver_check(
    solver: *const RmSolver,
    model_out: *mut *mut RmModel,
) -> i32 {
    if solver.is_null() {
        return RM_UNKNOWN;
    }
    let result = unsafe { (*solver).0.check() };
    sat_result_to_c(result, model_out)
}

// ---------------------------------------------------------------------------
// Model
// ---------------------------------------------------------------------------

/// # Safety
/// `model` must be a valid pointer returned by `rm_solver_check` or
/// `rm_solve_smtlib`.
#[no_mangle]
pub unsafe extern "C" fn rm_model_free(model: *mut RmModel) {
    if !model.is_null() {
        drop(unsafe { Box::from_raw(model) });
    }
}

/// Look up a bit-vector variable.  Returns `1` and writes `bits`/`width`
/// on success; returns `0` if the variable is absent or has a different sort.
///
/// # Safety
/// All pointers must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_model_get_bitvec(
    model: *const RmModel,
    name: *const c_char,
    bits_out: *mut u64,
    width_out: *mut u32,
) -> i32 {
    let (model, name) = match (model.is_null(), name.is_null()) {
        (false, false) => unsafe { (&(*model).0, CStr::from_ptr(name)) },
        _ => return 0,
    };
    match model.get_bitvec(name.to_str().unwrap_or("")) {
        Some((bits, width)) => {
            if !bits_out.is_null() {
                unsafe { *bits_out = bits };
            }
            if !width_out.is_null() {
                unsafe { *width_out = width };
            }
            1
        }
        None => 0,
    }
}

/// Look up an integer variable.  Returns `1` and writes `out` on success.
///
/// # Safety
/// All pointers must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_model_get_int(
    model: *const RmModel,
    name: *const c_char,
    out: *mut i64,
) -> i32 {
    let (model, name) = match (model.is_null(), name.is_null()) {
        (false, false) => unsafe { (&(*model).0, CStr::from_ptr(name)) },
        _ => return 0,
    };
    match model.get_int(name.to_str().unwrap_or("")) {
        Some(n) => {
            if !out.is_null() {
                unsafe { *out = n };
            }
            1
        }
        None => 0,
    }
}

/// Look up a Boolean variable.  Returns `1` and writes `out` (0=false, 1=true)
/// on success.
///
/// # Safety
/// All pointers must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_model_get_bool(
    model: *const RmModel,
    name: *const c_char,
    out: *mut u8,
) -> i32 {
    let (model, name) = match (model.is_null(), name.is_null()) {
        (false, false) => unsafe { (&(*model).0, CStr::from_ptr(name)) },
        _ => return 0,
    };
    match model.get_bool(name.to_str().unwrap_or("")) {
        Some(b) => {
            if !out.is_null() {
                unsafe { *out = b as u8 };
            }
            1
        }
        None => 0,
    }
}

/// Iterate all variable assignments.  Calls `callback(name, value_str, user_data)`
/// once per entry.  `value_str` is a null-terminated string in SMT-LIB 2 notation
/// (`"true"`, `"42"`, `"(_ bv5 8)"`).  Ownership of both strings stays with the
/// library; they are valid only for the duration of the callback.
///
/// # Safety
/// `model` must be valid and non-null.  `callback` must be a valid function pointer.
#[no_mangle]
pub unsafe extern "C" fn rm_model_iter(
    model: *const RmModel,
    callback: unsafe extern "C" fn(*const c_char, *const c_char, *mut std::ffi::c_void),
    user_data: *mut std::ffi::c_void,
) {
    if model.is_null() {
        return;
    }
    for (name, value) in unsafe { (*model).0.iter() } {
        let name_c = match CString::new(name) {
            Ok(s) => s,
            Err(_) => continue,
        };
        let val_str = value_to_smtlib(value);
        let val_c = match CString::new(val_str) {
            Ok(s) => s,
            Err(_) => continue,
        };
        unsafe { callback(name_c.as_ptr(), val_c.as_ptr(), user_data) };
    }
}

// ---------------------------------------------------------------------------
// Text interface (simplest integration path for Lean / TLC)
// ---------------------------------------------------------------------------

/// Solve an SMT-LIB 2 script supplied as a null-terminated C string.
/// Returns `RM_SAT` / `RM_UNSAT` / `RM_UNKNOWN`.
/// On `RM_SAT`, writes a heap-allocated model to `*model_out` if `model_out`
/// is non-null; the caller must free it with `rm_model_free`.
///
/// # Safety
/// `text` must be a valid null-terminated UTF-8 string.
/// `model_out` may be null.
#[no_mangle]
pub unsafe extern "C" fn rm_solve_smtlib(
    text: *const c_char,
    max_conflicts: u64,
    model_out: *mut *mut RmModel,
) -> i32 {
    if text.is_null() {
        return RM_UNKNOWN;
    }
    let s = match unsafe { CStr::from_ptr(text) }.to_str() {
        Ok(s) => s,
        Err(_) => return RM_UNKNOWN,
    };
    let budget = if max_conflicts == 0 {
        u64::MAX
    } else {
        max_conflicts
    };
    let result = solve_smtlib_with_budget(s, budget);
    sat_result_to_c(result, model_out)
}

/// Solve `count` SMT-LIB 2 scripts concurrently using `num_workers` threads.
/// `scripts[i]` is a null-terminated string; `results[i]` receives the result
/// code (`RM_SAT` / `RM_UNSAT` / `RM_UNKNOWN`).  Models are not returned
/// (use `rm_solve_smtlib` if you need models).
/// Returns the number of conclusive results (SAT or UNSAT).
///
/// # Safety
/// `scripts` must point to `count` valid null-terminated strings.
/// `results` must point to a writable array of at least `count` `int32_t`s.
#[no_mangle]
pub unsafe extern "C" fn rm_solve_batch(
    scripts: *const *const c_char,
    count: u32,
    num_workers: u32,
    max_conflicts: u64,
    results: *mut i32,
) -> u32 {
    if scripts.is_null() || results.is_null() || count == 0 {
        return 0;
    }
    let budget = if max_conflicts == 0 {
        u64::MAX
    } else {
        max_conflicts
    };

    let texts: Vec<String> = (0..count as usize)
        .filter_map(|i| {
            let ptr = unsafe { *scripts.add(i) };
            if ptr.is_null() {
                return None;
            }
            unsafe { CStr::from_ptr(ptr) }
                .to_str()
                .ok()
                .map(|s| s.to_owned())
        })
        .collect();

    let jobs: Vec<crate::pool::Job> = texts.iter().map(crate::pool::Job::new).collect();
    let pool = crate::pool::SolverPool::new(SolverConfig {
        num_workers: num_workers.max(1) as usize,
        max_conflicts: budget,
        timeout: None,
    });
    let outcomes = pool.run_all(jobs);

    let mut conclusive = 0u32;
    for (i, outcome) in outcomes.iter().enumerate() {
        let code = match &outcome.result {
            SatResult::Sat(_) | SatResult::Unsat => {
                conclusive += 1;
                sat_result_code(&outcome.result)
            }
            SatResult::Unknown(_) => RM_UNKNOWN,
        };
        unsafe { *results.add(i) = code };
    }
    conclusive
}

// ---------------------------------------------------------------------------
// Expression builders — leaves
// ---------------------------------------------------------------------------

/// # Safety
/// `ctx` and `name` must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_expr_bool_const(
    ctx: *const RmContext,
    name: *const c_char,
) -> *mut RmExpr {
    build_expr(ctx, name, |ctx, name| ctx.bool_const(name))
}

/// # Safety
/// `ctx` and `name` must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_expr_int_const(
    ctx: *const RmContext,
    name: *const c_char,
) -> *mut RmExpr {
    build_expr(ctx, name, |ctx, name| ctx.int_const(name))
}

/// # Safety
/// `ctx` and `name` must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_expr_bitvec_const(
    ctx: *const RmContext,
    name: *const c_char,
    width: u32,
) -> *mut RmExpr {
    build_expr(ctx, name, move |ctx, name| ctx.bitvec_const(name, width))
}

#[no_mangle]
pub extern "C" fn rm_expr_bool_val(_ctx: *const RmContext, b: u8) -> *mut RmExpr {
    let ctx = Context::new();
    Box::into_raw(Box::new(RmExpr(ctx.bool_val(b != 0))))
}

#[no_mangle]
pub extern "C" fn rm_expr_int_val(_ctx: *const RmContext, n: i64) -> *mut RmExpr {
    let ctx = Context::new();
    Box::into_raw(Box::new(RmExpr(ctx.int_val(n))))
}

#[no_mangle]
pub extern "C" fn rm_expr_bitvec_val(
    _ctx: *const RmContext,
    value: u64,
    width: u32,
) -> *mut RmExpr {
    let ctx = Context::new();
    Box::into_raw(Box::new(RmExpr(ctx.bitvec_val(value, width))))
}

/// # Safety
/// `expr` must be a valid non-null pointer.
#[no_mangle]
pub unsafe extern "C" fn rm_expr_free(expr: *mut RmExpr) {
    if !expr.is_null() {
        drop(unsafe { Box::from_raw(expr) });
    }
}

// ---------------------------------------------------------------------------
// Expression builders — Boolean connectives
// ---------------------------------------------------------------------------

wrap_unary!(rm_expr_not, not);
wrap_binary!(rm_expr_and, and);
wrap_binary!(rm_expr_or, or);
wrap_binary!(rm_expr_implies, implies);
wrap_binary!(rm_expr_iff, iff);
wrap_binary!(rm_expr_eq, eq);
wrap_binary!(rm_expr_distinct, distinct);

/// If-then-else.
///
/// # Safety
/// All pointers must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_expr_ite(
    _ctx: *const RmContext,
    cond: *const RmExpr,
    then_: *const RmExpr,
    else_: *const RmExpr,
) -> *mut RmExpr {
    if cond.is_null() || then_.is_null() || else_.is_null() {
        return std::ptr::null_mut();
    }
    let e = unsafe { (*cond).0.ite(&(*then_).0, &(*else_).0) };
    Box::into_raw(Box::new(RmExpr(e)))
}

// ---------------------------------------------------------------------------
// Expression builders — integer arithmetic
// ---------------------------------------------------------------------------

wrap_binary!(rm_expr_add, add);
wrap_binary!(rm_expr_sub, sub);
wrap_binary!(rm_expr_mul, mul);
wrap_unary!(rm_expr_neg, neg);
wrap_binary!(rm_expr_lt, lt);
wrap_binary!(rm_expr_le, le);
wrap_binary!(rm_expr_gt, gt);
wrap_binary!(rm_expr_ge, ge);

// ---------------------------------------------------------------------------
// Expression builders — bit-vector
// ---------------------------------------------------------------------------

wrap_binary!(rm_expr_bvadd, bvadd);
wrap_binary!(rm_expr_bvsub, bvsub);
wrap_binary!(rm_expr_bvmul, bvmul);
wrap_unary!(rm_expr_bvneg, bvneg);
wrap_binary!(rm_expr_bvand, bvand);
wrap_binary!(rm_expr_bvor, bvor);
wrap_binary!(rm_expr_bvxor, bvxor);
wrap_unary!(rm_expr_bvnot, bvnot);
wrap_binary!(rm_expr_bvult, bvult);
wrap_binary!(rm_expr_bvule, bvule);
wrap_binary!(rm_expr_bvslt, bvslt);
wrap_binary!(rm_expr_bvsle, bvsle);
wrap_binary!(rm_expr_bvshl, bvshl);
wrap_binary!(rm_expr_bvlshr, bvlshr);
wrap_binary!(rm_expr_bvashr, bvashr);
wrap_binary!(rm_expr_concat, concat);

/// # Safety
/// `expr` must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_expr_extract(
    _ctx: *const RmContext,
    hi: u32,
    lo: u32,
    expr: *const RmExpr,
) -> *mut RmExpr {
    if expr.is_null() {
        return std::ptr::null_mut();
    }
    Box::into_raw(Box::new(RmExpr(unsafe { (*expr).0.extract(hi, lo) })))
}

/// # Safety
/// `expr` must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_expr_zero_extend(
    _ctx: *const RmContext,
    extra_bits: u32,
    expr: *const RmExpr,
) -> *mut RmExpr {
    if expr.is_null() {
        return std::ptr::null_mut();
    }
    Box::into_raw(Box::new(RmExpr(unsafe {
        (*expr).0.zero_extend(extra_bits)
    })))
}

/// # Safety
/// `expr` must be valid and non-null.
#[no_mangle]
pub unsafe extern "C" fn rm_expr_sign_extend(
    _ctx: *const RmContext,
    extra_bits: u32,
    expr: *const RmExpr,
) -> *mut RmExpr {
    if expr.is_null() {
        return std::ptr::null_mut();
    }
    Box::into_raw(Box::new(RmExpr(unsafe {
        (*expr).0.sign_extend(extra_bits)
    })))
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn sat_result_to_c(result: SatResult, model_out: *mut *mut RmModel) -> i32 {
    match result {
        SatResult::Sat(model) => {
            if !model_out.is_null() {
                unsafe { *model_out = Box::into_raw(Box::new(RmModel(model))) };
            }
            RM_SAT
        }
        SatResult::Unsat => {
            if !model_out.is_null() {
                unsafe { *model_out = std::ptr::null_mut() };
            }
            RM_UNSAT
        }
        SatResult::Unknown(_) => {
            if !model_out.is_null() {
                unsafe { *model_out = std::ptr::null_mut() };
            }
            RM_UNKNOWN
        }
    }
}

fn sat_result_code(r: &SatResult) -> i32 {
    match r {
        SatResult::Sat(_) => RM_SAT,
        SatResult::Unsat => RM_UNSAT,
        SatResult::Unknown(_) => RM_UNKNOWN,
    }
}

fn value_to_smtlib(value: &Value) -> String {
    match value {
        Value::Bool(b) => if *b { "true" } else { "false" }.to_owned(),
        Value::Int(n) => {
            if *n < 0 {
                format!("(- {})", n.unsigned_abs())
            } else {
                n.to_string()
            }
        }
        Value::BitVec { bits, width } => format!("(_ bv{bits} {width})"),
    }
}

unsafe fn build_expr(
    ctx: *const RmContext,
    name: *const c_char,
    f: impl FnOnce(&Context, &str) -> Expr,
) -> *mut RmExpr {
    if ctx.is_null() || name.is_null() {
        return std::ptr::null_mut();
    }
    let ctx_ref = unsafe { &(*ctx).0 };
    let name_str = match unsafe { CStr::from_ptr(name) }.to_str() {
        Ok(s) => s,
        Err(_) => return std::ptr::null_mut(),
    };
    Box::into_raw(Box::new(RmExpr(f(ctx_ref, name_str))))
}

macro_rules! wrap_unary {
    ($fn_name:ident, $method:ident) => {
        /// # Safety
        /// `a` must be a valid non-null pointer to an `RmExpr` allocated by this library.
        #[no_mangle]
        pub unsafe extern "C" fn $fn_name(_ctx: *const RmContext, a: *const RmExpr) -> *mut RmExpr {
            if a.is_null() {
                return std::ptr::null_mut();
            }
            Box::into_raw(Box::new(RmExpr(unsafe { (*a).0.$method() })))
        }
    };
}

macro_rules! wrap_binary {
    ($fn_name:ident, $method:ident) => {
        /// # Safety
        /// `a` and `b` must be valid non-null pointers to `RmExpr` values allocated by this library.
        #[no_mangle]
        pub unsafe extern "C" fn $fn_name(
            _ctx: *const RmContext,
            a: *const RmExpr,
            b: *const RmExpr,
        ) -> *mut RmExpr {
            if a.is_null() || b.is_null() {
                return std::ptr::null_mut();
            }
            Box::into_raw(Box::new(RmExpr(unsafe { (*a).0.$method(&(*b).0) })))
        }
    };
}

use wrap_binary;
use wrap_unary;

// ---------------------------------------------------------------------------
// FFI tests (Rust-side, exercising the C functions via unsafe calls)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;
    use std::ptr;

    fn cstr(s: &str) -> CString {
        CString::new(s).unwrap()
    }

    #[test]
    fn ffi_bv_sat() {
        unsafe {
            let ctx = rm_context_new();
            let x = rm_expr_bitvec_const(ctx, cstr("x").as_ptr(), 8);
            let five = rm_expr_bitvec_val(ctx, 5, 8);
            let cmp = rm_expr_bvult(ctx, x, five);
            let s = rm_solver_new(ctx, 1, 0);
            rm_solver_assert(s, cmp);
            rm_expr_free(x);
            rm_expr_free(five);
            rm_expr_free(cmp);

            let mut model: *mut RmModel = ptr::null_mut();
            let r = rm_solver_check(s, &mut model);
            assert_eq!(r, RM_SAT);
            assert!(!model.is_null());

            let mut bits: u64 = 999;
            let mut width: u32 = 0;
            assert_eq!(
                rm_model_get_bitvec(model, cstr("x").as_ptr(), &mut bits, &mut width),
                1
            );
            assert!(bits < 5, "model x={bits} must be < 5");
            assert_eq!(width, 8);

            rm_model_free(model);
            rm_solver_free(s);
            rm_context_free(ctx);
        }
    }

    #[test]
    fn ffi_bv_unsat() {
        unsafe {
            let ctx = rm_context_new();
            let x = rm_expr_bitvec_const(ctx, cstr("x").as_ptr(), 4);
            let zero = rm_expr_bitvec_val(ctx, 0, 4);
            let ones = rm_expr_bitvec_val(ctx, 15, 4);
            let e0 = rm_expr_eq(ctx, x, zero);
            let e1 = rm_expr_eq(ctx, x, ones);
            let s = rm_solver_new(ctx, 1, 0);
            rm_solver_assert(s, e0);
            rm_solver_assert(s, e1);
            rm_expr_free(x);
            rm_expr_free(zero);
            rm_expr_free(ones);
            rm_expr_free(e0);
            rm_expr_free(e1);

            let r = rm_solver_check(s, ptr::null_mut());
            assert_eq!(r, RM_UNSAT);
            rm_solver_free(s);
            rm_context_free(ctx);
        }
    }

    #[test]
    fn ffi_push_pop() {
        unsafe {
            let ctx = rm_context_new();
            let x = rm_expr_bitvec_const(ctx, cstr("x").as_ptr(), 8);
            let hundred = rm_expr_bitvec_val(ctx, 100, 8);
            let zero = rm_expr_bitvec_val(ctx, 0, 8);
            let s = rm_solver_new(ctx, 1, 0);

            rm_solver_assert(s, rm_expr_bvult(ctx, x, hundred));
            rm_solver_push(s);
            rm_solver_assert(s, rm_expr_bvult(ctx, x, zero));
            assert_eq!(rm_solver_check(s, ptr::null_mut()), RM_UNSAT);
            rm_solver_pop(s);
            assert_eq!(rm_solver_check(s, ptr::null_mut()), RM_SAT);

            rm_expr_free(x);
            rm_expr_free(hundred);
            rm_expr_free(zero);
            rm_solver_free(s);
            rm_context_free(ctx);
        }
    }

    #[test]
    fn ffi_solve_smtlib_text() {
        let script = cstr(
            "(set-logic QF_BV)\n(declare-const a (_ BitVec 4))\n(assert (= a #b0101))\n(check-sat)",
        );
        unsafe {
            let mut model: *mut RmModel = ptr::null_mut();
            let r = rm_solve_smtlib(script.as_ptr(), 0, &mut model);
            assert_eq!(r, RM_SAT);
            let mut bits: u64 = 0;
            let mut width: u32 = 0;
            assert_eq!(
                rm_model_get_bitvec(model, cstr("a").as_ptr(), &mut bits, &mut width),
                1
            );
            assert_eq!(bits, 5);
            rm_model_free(model);
        }
    }

    #[test]
    fn ffi_batch_solve() {
        let s0 = cstr(
            "(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (bvult x #x5))(check-sat)",
        );
        let s1 = cstr("(set-logic QF_BV)(declare-const x (_ BitVec 4))(assert (= x #b0000))(assert (= x #b1111))(check-sat)");
        let ptrs = [s0.as_ptr(), s1.as_ptr()];
        let mut results = [RM_UNKNOWN; 2];
        unsafe {
            let conclusive = rm_solve_batch(ptrs.as_ptr(), 2, 2, 0, results.as_mut_ptr());
            assert_eq!(conclusive, 2);
        }
        assert_eq!(results[0], RM_SAT);
        assert_eq!(results[1], RM_UNSAT);
    }

    #[test]
    fn ffi_null_safety() {
        unsafe {
            assert_eq!(rm_solver_check(ptr::null(), ptr::null_mut()), RM_UNKNOWN);
            rm_solver_assert(ptr::null_mut(), ptr::null());
            rm_context_free(ptr::null_mut());
            rm_model_free(ptr::null_mut());
        }
    }
}
