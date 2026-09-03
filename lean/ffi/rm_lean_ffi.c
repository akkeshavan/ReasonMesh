/*
 * rm_lean_ffi.c — Lean 4 runtime wrappers for the ReasonMesh C FFI.
 *
 * Each Lean `@[extern]` function follows Lean 4's calling convention:
 *   - IO functions receive the world token as a final `lean_obj_arg` and
 *     return `lean_io_result_mk_ok(value)`.
 *   - Opaque C objects are wrapped in `lean_external_class` so Lean's GC
 *     calls the finalizer when the object goes out of scope.
 *   - Borrowed string arguments use `lean_string_cstr` (no ownership transfer).
 *
 * Build: compiled by Lake as part of the RmApi extern_lib declaration.
 * Link:  the resulting .o is linked together with librm_api.{dylib,so}.
 */

#include <lean/lean.h>
#include <rm_api.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

/* ── ExternalObject classes (one per opaque C type) ──────────────────────── */

static lean_external_class *g_ctx_cls    = NULL;
static lean_external_class *g_solver_cls = NULL;
static lean_external_class *g_expr_cls   = NULL;
static lean_external_class *g_model_cls  = NULL;

static void ctx_fin(void *p)    { rm_context_free((rm_context_t *)p); }
static void solver_fin(void *p) { rm_solver_free((rm_solver_t *)p); }
static void expr_fin(void *p)   { rm_expr_free((rm_expr_t *)p); }
static void model_fin(void *p)  { rm_model_free((rm_model_t *)p); }
static void noop_foreach(void *p, b_lean_obj_arg f) { (void)p; (void)f; }

/* Called once by Lake/Lean when the library is loaded (via `initialize`). */
LEAN_EXPORT lean_obj_res rm_lean_initialize(uint8_t builtin, lean_obj_arg world) {
    (void)builtin;
    g_ctx_cls    = lean_register_external_class(ctx_fin,    noop_foreach);
    g_solver_cls = lean_register_external_class(solver_fin, noop_foreach);
    g_expr_cls   = lean_register_external_class(expr_fin,   noop_foreach);
    g_model_cls  = lean_register_external_class(model_fin,  noop_foreach);
    return lean_io_result_mk_ok(lean_box(0));
}

/* ── Helpers ──────────────────────────────────────────────────────────────── */

static lean_object *mk_some(lean_obj_arg v) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, v);
    return o;
}

static lean_object *mk_none(void) {
    return lean_box(0);
}

static lean_object *mk_pair(lean_obj_arg a, lean_obj_arg b) {
    lean_object *p = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(p, 0, a);
    lean_ctor_set(p, 1, b);
    return p;
}

/* ── Context ──────────────────────────────────────────────────────────────── */

LEAN_EXPORT lean_obj_res rm_context_new_lean(lean_obj_arg world) {
    rm_context_t *ctx = rm_context_new();
    return lean_io_result_mk_ok(lean_alloc_external(g_ctx_cls, ctx));
}

/* ── Solver ───────────────────────────────────────────────────────────────── */

LEAN_EXPORT lean_obj_res rm_solver_new_lean(lean_obj_arg ctx_obj,
                                             uint32_t num_workers,
                                             uint64_t max_conflicts,
                                             lean_obj_arg world) {
    rm_context_t *ctx = (rm_context_t *)lean_get_external_data(ctx_obj);
    rm_solver_t  *s   = rm_solver_new(ctx, num_workers, max_conflicts);
    return lean_io_result_mk_ok(lean_alloc_external(g_solver_cls, s));
}

LEAN_EXPORT lean_obj_res rm_solver_assert_lean(lean_obj_arg solver_obj,
                                                lean_obj_arg expr_obj,
                                                lean_obj_arg world) {
    rm_solver_assert((rm_solver_t *)lean_get_external_data(solver_obj),
                     (rm_expr_t  *)lean_get_external_data(expr_obj));
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res rm_solver_push_lean(lean_obj_arg solver_obj,
                                              lean_obj_arg world) {
    rm_solver_push((rm_solver_t *)lean_get_external_data(solver_obj));
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res rm_solver_pop_lean(lean_obj_arg solver_obj,
                                             lean_obj_arg world) {
    rm_solver_pop((rm_solver_t *)lean_get_external_data(solver_obj));
    return lean_io_result_mk_ok(lean_box(0));
}

/* Returns (UInt32 × Option RmModel): code + optional model. */
LEAN_EXPORT lean_obj_res rm_solver_check_lean(lean_obj_arg solver_obj,
                                               lean_obj_arg world) {
    rm_model_t *model = NULL;
    int32_t r = rm_solver_check((rm_solver_t *)lean_get_external_data(solver_obj),
                                &model);
    lean_object *model_opt = (r == RM_SAT && model)
        ? mk_some(lean_alloc_external(g_model_cls, model))
        : mk_none();
    return lean_io_result_mk_ok(mk_pair(lean_box_uint32((uint32_t)r), model_opt));
}

/* ── Model ────────────────────────────────────────────────────────────────── */

LEAN_EXPORT lean_obj_res rm_model_get_bitvec_lean(lean_obj_arg model_obj,
                                                    b_lean_obj_arg name_obj,
                                                    lean_obj_arg world) {
    uint64_t bits  = 0;
    uint32_t width = 0;
    int ok = rm_model_get_bitvec((rm_model_t *)lean_get_external_data(model_obj),
                                  lean_string_cstr(name_obj), &bits, &width);
    lean_object *opt = ok
        ? mk_some(mk_pair(lean_box_uint64(bits), lean_box_uint32(width)))
        : mk_none();
    return lean_io_result_mk_ok(opt);
}

LEAN_EXPORT lean_obj_res rm_model_get_int_lean(lean_obj_arg model_obj,
                                                b_lean_obj_arg name_obj,
                                                lean_obj_arg world) {
    int64_t val = 0;
    int ok = rm_model_get_int((rm_model_t *)lean_get_external_data(model_obj),
                               lean_string_cstr(name_obj), &val);
    lean_object *opt = ok ? mk_some(lean_box_int64(val)) : mk_none();
    return lean_io_result_mk_ok(opt);
}

/* ── Model iteration ─────────────────────────────────────────────────────── */

typedef struct { char *buf; size_t cap; size_t len; } strbuf_t;

static void strbuf_append(strbuf_t *b, const char *s) {
    size_t n = strlen(s);
    if (b->len + n + 1 >= b->cap) {
        b->cap = (b->cap + n + 1) * 2;
        b->buf = realloc(b->buf, b->cap);
    }
    memcpy(b->buf + b->len, s, n);
    b->len += n;
    b->buf[b->len] = '\0';
}

static void model_collect_cb(const char *name, const char *value, void *ud) {
    strbuf_t *b = (strbuf_t *)ud;
    strbuf_append(b, "(");
    strbuf_append(b, name);
    strbuf_append(b, " ");
    strbuf_append(b, value);
    strbuf_append(b, ")");
}

/* Returns the model as an SMT-LIB get-model style string. */
LEAN_EXPORT lean_obj_res rm_model_to_string_lean(lean_obj_arg model_obj,
                                                   lean_obj_arg world) {
    strbuf_t buf = { .buf = malloc(256), .cap = 256, .len = 0 };
    buf.buf[0] = '\0';
    rm_model_iter((rm_model_t *)lean_get_external_data(model_obj),
                  model_collect_cb, &buf);
    lean_object *s = lean_mk_string(buf.buf);
    free(buf.buf);
    return lean_io_result_mk_ok(s);
}

/* ── Text interface ───────────────────────────────────────────────────────── */

/*
 * Returns (UInt32 × String): result code + model string (empty if not SAT).
 * This is the primary entry point for the rm_decide tactic — no pointer
 * lifetime issues, no ExternalObject on the Lean side.
 */
LEAN_EXPORT lean_obj_res rm_solve_smtlib_lean(b_lean_obj_arg script_obj,
                                               uint64_t max_conflicts,
                                               lean_obj_arg world) {
    uint64_t budget  = (max_conflicts == 0) ? UINT64_MAX : max_conflicts;
    rm_model_t *model = NULL;
    int32_t r = rm_solve_smtlib(lean_string_cstr(script_obj), budget, &model);

    char *model_str = NULL;
    if (r == RM_SAT && model) {
        strbuf_t buf = { .buf = malloc(256), .cap = 256, .len = 0 };
        buf.buf[0] = '\0';
        rm_model_iter(model, model_collect_cb, &buf);
        model_str = buf.buf;
        rm_model_free(model);
    }
    lean_object *model_lean = lean_mk_string(model_str ? model_str : "");
    if (model_str) free(model_str);
    return lean_io_result_mk_ok(mk_pair(lean_box_uint32((uint32_t)r), model_lean));
}

/* ── Batch / proof farm ───────────────────────────────────────────────────── */

/*
 * Takes a Lean `Array String`, returns a Lean `Array UInt32`.
 * The Lean caller is responsible for array ownership (borrowed via b_ prefix).
 */
LEAN_EXPORT lean_obj_res rm_solve_batch_lean(b_lean_obj_arg scripts_obj,
                                              uint32_t num_workers,
                                              uint64_t max_conflicts,
                                              lean_obj_arg world) {
    uint32_t count  = (uint32_t)lean_array_size(scripts_obj);
    uint64_t budget = (max_conflicts == 0) ? UINT64_MAX : max_conflicts;

    const char **scripts = (const char **)alloca(count * sizeof(char *));
    for (uint32_t i = 0; i < count; i++) {
        lean_object *s = lean_array_uget(scripts_obj, i);
        scripts[i] = lean_string_cstr(s);
    }

    int32_t *results = (int32_t *)alloca(count * sizeof(int32_t));
    rm_solve_batch(scripts, count, num_workers, budget, results);

    lean_object *arr = lean_alloc_array(count, count);
    for (uint32_t i = 0; i < count; i++) {
        lean_array_uset(arr, i, lean_box_uint32((uint32_t)results[i]));
    }
    return lean_io_result_mk_ok(arr);
}

/* ── Expression builders ──────────────────────────────────────────────────── */

LEAN_EXPORT lean_obj_res rm_expr_bitvec_const_lean(lean_obj_arg ctx_obj,
                                                    b_lean_obj_arg name_obj,
                                                    uint32_t width,
                                                    lean_obj_arg world) {
    rm_context_t *ctx = (rm_context_t *)lean_get_external_data(ctx_obj);
    rm_expr_t *e = rm_expr_bitvec_const(ctx, lean_string_cstr(name_obj), width);
    return lean_io_result_mk_ok(lean_alloc_external(g_expr_cls, e));
}

LEAN_EXPORT lean_obj_res rm_expr_int_const_lean(lean_obj_arg ctx_obj,
                                                 b_lean_obj_arg name_obj,
                                                 lean_obj_arg world) {
    rm_context_t *ctx = (rm_context_t *)lean_get_external_data(ctx_obj);
    rm_expr_t *e = rm_expr_int_const(ctx, lean_string_cstr(name_obj));
    return lean_io_result_mk_ok(lean_alloc_external(g_expr_cls, e));
}

LEAN_EXPORT lean_obj_res rm_expr_bool_const_lean(lean_obj_arg ctx_obj,
                                                  b_lean_obj_arg name_obj,
                                                  lean_obj_arg world) {
    rm_context_t *ctx = (rm_context_t *)lean_get_external_data(ctx_obj);
    rm_expr_t *e = rm_expr_bool_const(ctx, lean_string_cstr(name_obj));
    return lean_io_result_mk_ok(lean_alloc_external(g_expr_cls, e));
}
