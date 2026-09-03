/*
 * rm_api.h — C header for the ReasonMesh solver library.
 *
 * Link against:  librm_api.dylib  (macOS)
 *                librm_api.so     (Linux)
 *                rm_api.dll       (Windows)
 *
 * Build the shared library:
 *   cargo build --release -p rm-api
 *   # → target/release/librm_api.{dylib,so}
 *
 * Lean 4 integration (lakefile.lean):
 *   extern_lib "rm_api" := inputFile "path/to/librm_api.dylib"
 *
 * Lean 4 bindings skeleton:
 * ─────────────────────────────────────────────────────────────────────────────
 *   def RmContext := USize
 *   def RmSolver  := USize
 *   def RmExpr    := USize
 *   def RmModel   := USize
 *
 *   @[extern "rm_context_new"]  opaque rmContextNew  (_ : Unit) : RmContext
 *   @[extern "rm_context_free"] opaque rmContextFree (ctx : RmContext) : Unit
 *
 *   @[extern "rm_solver_new"]
 *   opaque rmSolverNew (ctx : RmContext) (workers : UInt32) (budget : UInt64) : RmSolver
 *   @[extern "rm_solver_free"]   opaque rmSolverFree   (s : RmSolver) : Unit
 *   @[extern "rm_solver_assert"] opaque rmSolverAssert (s : RmSolver) (e : RmExpr) : Unit
 *   @[extern "rm_solver_push"]   opaque rmSolverPush   (s : RmSolver) : Unit
 *   @[extern "rm_solver_pop"]    opaque rmSolverPop    (s : RmSolver) : Unit
 *
 *   -- Returns 0=SAT 1=UNSAT 2=UNKNOWN; writes model pointer into out[0].
 *   @[extern "rm_solver_check"]
 *   opaque rmSolverCheck (s : RmSolver) (modelOut : ByteArray) : Int32
 *
 *   @[extern "rm_solve_smtlib"]
 *   opaque rmSolveSmtlib (text : @& String) (budget : UInt64)
 *                         (modelOut : ByteArray) : Int32
 *
 *   @[extern "rm_solve_batch"]
 *   opaque rmSolveBatch (scripts : @& Array String) (n : UInt32)
 *                        (workers : UInt32) (budget : UInt64)
 *                        (results : ByteArray) : UInt32
 * ─────────────────────────────────────────────────────────────────────────────
 *
 * Memory ownership:
 *   All `rm_*_new` / `rm_*_const` / `rm_*_val` functions allocate; the caller
 *   MUST call the matching `rm_*_free`.  Expressions passed to `rm_solver_assert`
 *   are cloned internally; the caller may free the expression immediately after.
 */

#ifndef RM_API_H
#define RM_API_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ── Result codes ─────────────────────────────────────────────────────────── */
#define RM_SAT     0
#define RM_UNSAT   1
#define RM_UNKNOWN 2

/* ── Opaque handle types ──────────────────────────────────────────────────── */
typedef struct rm_context rm_context_t;
typedef struct rm_solver  rm_solver_t;
typedef struct rm_expr    rm_expr_t;
typedef struct rm_model   rm_model_t;

/* ── Context ──────────────────────────────────────────────────────────────── */
rm_context_t *rm_context_new(void);
void          rm_context_free(rm_context_t *ctx);

/* ── Solver ───────────────────────────────────────────────────────────────── */
/* num_workers: solver threads to race (1 = single-threaded).                 */
/* max_conflicts: CDCL budget per thread; 0 = unlimited.                      */
rm_solver_t *rm_solver_new(rm_context_t *ctx, uint32_t num_workers,
                            uint64_t max_conflicts);
void         rm_solver_free(rm_solver_t *s);
void         rm_solver_assert(rm_solver_t *s, rm_expr_t *expr);
void         rm_solver_push(rm_solver_t *s);
void         rm_solver_pop(rm_solver_t *s);

/* Returns RM_SAT / RM_UNSAT / RM_UNKNOWN.                                    */
/* On RM_SAT, *model_out is set to a heap-allocated model (free with          */
/* rm_model_free). On other results *model_out is set to NULL.                */
/* model_out may be NULL if the model is not needed.                          */
int32_t rm_solver_check(rm_solver_t *s, rm_model_t **model_out);

/* ── Model ────────────────────────────────────────────────────────────────── */
void    rm_model_free(rm_model_t *m);

/* All getters return 1 on success, 0 if the variable is absent or has a      */
/* different sort.                                                             */
int32_t rm_model_get_bitvec(rm_model_t *m, const char *name,
                             uint64_t *bits_out, uint32_t *width_out);
int32_t rm_model_get_int(rm_model_t *m, const char *name, int64_t *out);
int32_t rm_model_get_bool(rm_model_t *m, const char *name, uint8_t *out);

/* Iterate all assignments.  callback(name, smtlib_value, user_data) is       */
/* called once per variable; both string pointers are valid only for the      */
/* duration of the callback.                                                  */
void rm_model_iter(rm_model_t *m,
                   void (*callback)(const char *name, const char *value,
                                    void *user_data),
                   void *user_data);

/* ── Text interface ───────────────────────────────────────────────────────── */
/* Solve an SMT-LIB 2 script.  text must be null-terminated UTF-8.            */
/* model_out follows the same semantics as rm_solver_check.                   */
int32_t rm_solve_smtlib(const char *text, uint64_t max_conflicts,
                         rm_model_t **model_out);

/* Concurrent proof farm: solve count scripts using num_workers threads.      */
/* results[i] receives RM_SAT / RM_UNSAT / RM_UNKNOWN for scripts[i].        */
/* Models are not returned; use rm_solve_smtlib for per-query models.         */
/* Returns the number of conclusive results.                                  */
uint32_t rm_solve_batch(const char **scripts, uint32_t count,
                         uint32_t num_workers, uint64_t max_conflicts,
                         int32_t *results);

/* ── Expression builders — leaves ────────────────────────────────────────── */
rm_expr_t *rm_expr_bool_const(rm_context_t *ctx, const char *name);
rm_expr_t *rm_expr_int_const(rm_context_t *ctx, const char *name);
rm_expr_t *rm_expr_bitvec_const(rm_context_t *ctx, const char *name,
                                 uint32_t width);
rm_expr_t *rm_expr_bool_val(rm_context_t *ctx, uint8_t b);
rm_expr_t *rm_expr_int_val(rm_context_t *ctx, int64_t n);
rm_expr_t *rm_expr_bitvec_val(rm_context_t *ctx, uint64_t value, uint32_t width);
void       rm_expr_free(rm_expr_t *e);

/* ── Expression builders — Boolean connectives ────────────────────────────── */
rm_expr_t *rm_expr_not(rm_context_t *ctx, rm_expr_t *a);
rm_expr_t *rm_expr_and(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_or(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_implies(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_iff(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_ite(rm_context_t *ctx, rm_expr_t *cond, rm_expr_t *then_,
                        rm_expr_t *else_);
rm_expr_t *rm_expr_eq(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_distinct(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);

/* ── Expression builders — integer arithmetic ─────────────────────────────── */
rm_expr_t *rm_expr_add(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_sub(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_mul(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_neg(rm_context_t *ctx, rm_expr_t *a);
rm_expr_t *rm_expr_lt(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_le(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_gt(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_ge(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);

/* ── Expression builders — bit-vector ────────────────────────────────────── */
rm_expr_t *rm_expr_bvadd(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvsub(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvmul(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvneg(rm_context_t *ctx, rm_expr_t *a);
rm_expr_t *rm_expr_bvand(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvor(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvxor(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvnot(rm_context_t *ctx, rm_expr_t *a);
rm_expr_t *rm_expr_bvult(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvule(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvslt(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvsle(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvshl(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvlshr(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_bvashr(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_concat(rm_context_t *ctx, rm_expr_t *a, rm_expr_t *b);
rm_expr_t *rm_expr_extract(rm_context_t *ctx, uint32_t hi, uint32_t lo,
                             rm_expr_t *e);
rm_expr_t *rm_expr_zero_extend(rm_context_t *ctx, uint32_t extra_bits,
                                rm_expr_t *e);
rm_expr_t *rm_expr_sign_extend(rm_context_t *ctx, uint32_t extra_bits,
                                rm_expr_t *e);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* RM_API_H */
