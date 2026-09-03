//! Exhaustive differential tests: the bit-blasted circuit for a BV operator
//! must agree with reference `u64` arithmetic on every small-width input.

use crate::blaster::Blaster;
use rm_ir::{Builder, Node, NodeId};
use rm_syntax::Script;

/// Blast `(assert (op a b))` and evaluate the single root gate under the
/// assignment `a = av, b = bv` (bits LSB first). Returns the gate value.
fn eval_op(op: &str, width: u32, av: u64, bv: u64) -> bool {
    let script = format!(
        "(declare-const a (_ BitVec {width}))
         (declare-const b (_ BitVec {width}))
         (assert ({op} a b))"
    );
    let s = Script::parse(&script).unwrap();
    let mut builder = Builder::new();
    let mut root = None;
    for a in s.assertions() {
        root = Some(builder.lower(a));
    }
    let root = root.unwrap();
    let mut blaster = Blaster::new();
    let bits = blaster.blast(&builder.dag, root);
    let inputs = build_inputs(&builder.dag, root, width, av, bv);
    let vals = blaster.circuit.evaluate(&inputs);
    vals[bits[0].0 as usize]
}

/// Compute the input vector for the blaster given a root that mentions two
/// BV vars a and b. We rely on the fact that a and b are blasted in order of
/// first appearance; we recover their input indexes by re-walking.
fn build_inputs(dag: &rm_ir::TermDag, root: NodeId, width: u32, av: u64, bv: u64) -> Vec<bool> {
    let mut order: Vec<u32> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    collect_vars(dag, root, &mut order, &mut seen);
    let mut inputs = vec![false; (order.len() * width as usize).max(width as usize * 2)];
    for (vi, &vid) in order.iter().enumerate() {
        let val = if vid == 0 { av } else { bv };
        for b in 0..width as usize {
            inputs[vi * width as usize + b] = val & (1 << b) != 0;
        }
    }
    inputs
}

fn collect_vars(
    dag: &rm_ir::TermDag,
    id: NodeId,
    order: &mut Vec<u32>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match dag.get(id) {
        Node::BvVar { id: vid, .. } | Node::BoolVar { id: vid } => {
            if !seen.insert(*vid) {
                return;
            }
            order.push(*vid);
        }
        Node::Apply { children, .. } => {
            for c in children {
                collect_vars(dag, *c, order, seen);
            }
        }
        _ => {}
    }
}

/// Reference implementations (u64, truncated to `width` bits).
fn ref_bv(op: &str, width: u32, av: u64, bv: u64) -> bool {
    let mask = if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let a = av & mask;
    let b = bv & mask;
    let sign = |v: u64| -> i64 {
        let sign_bit = 1u64 << (width - 1);
        if v & sign_bit != 0 {
            (v | !mask) as i64
        } else {
            v as i64
        }
    };
    let unsigned_lt = a < b;
    match op {
        "bvult" => unsigned_lt,
        "bvule" => a <= b,
        "bvugt" => a > b,
        "bvuge" => a >= b,
        "bvslt" => sign(a) < sign(b),
        "bvsle" => sign(a) <= sign(b),
        "bvsgt" => sign(a) > sign(b),
        "bvsge" => sign(a) >= sign(b),
        _ => unreachable!("no reference for {op}"),
    }
}

fn test_compare(op: &str, width: u32) {
    let max = 1u64 << width.min(4);
    for av in 0..max {
        for bv in 0..max {
            let got = eval_op(op, width, av, bv);
            let want = ref_bv(op, width, av, bv);
            assert_eq!(got, want, "{op} width {width}: a={av} b={bv}");
        }
    }
}

#[test]
fn differential_ult() {
    test_compare("bvult", 2);
    test_compare("bvult", 3);
}

#[test]
fn differential_ule_ugt_uge() {
    for op in ["bvule", "bvugt", "bvuge"] {
        test_compare(op, 3);
    }
}

#[test]
fn differential_signed() {
    for op in ["bvslt", "bvsle", "bvsgt", "bvsge"] {
        test_compare(op, 3);
    }
}

#[test]
fn differential_addition_circuit_eval() {
    // a + b == c is blasted; evaluate the equality gate for small inputs.
    for width in [2u32, 3u32] {
        for av in 0..(1u64 << width) {
            for bv in 0..(1u64 << width) {
                // (a + b) == a + b is always true.
                let eq_true = eval_add_eq(width, av, bv, (av + bv) & mask(width));
                assert!(eq_true, "a={av} b={bv} w={width}");
                // (a + b) == a + b + 1 is always false.
                let eq_false = eval_add_eq(width, av, bv, ((av + bv) & mask(width)) ^ 1);
                assert!(!eq_false, "a={av} b={bv} w={width}");
            }
        }
    }
}

fn mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

fn eval_add_eq(width: u32, av: u64, bv: u64, want: u64) -> bool {
    let bits = format!("{want:0w$b}", w = width as usize);
    let script = format!(
        "(declare-const a (_ BitVec {width}))
         (declare-const b (_ BitVec {width}))
         (assert (= (bvadd a b) #b{bits}))"
    );
    let s = Script::parse(&script).unwrap();
    let mut builder = Builder::new();
    let mut root = None;
    for a in s.assertions() {
        root = Some(builder.lower(a));
    }
    let root = root.unwrap();
    let mut blaster = Blaster::new();
    let bits = blaster.blast(&builder.dag, root);
    let inputs = build_inputs(&builder.dag, root, width, av, bv);
    let vals = blaster.circuit.evaluate(&inputs);
    vals[bits[0].0 as usize]
}

#[test]
fn differential_add_literal_consistency() {
    // Direct: (bvadd a b) must produce (a+b) mod 2^w. We verify through the
    // equality test above plus a small direct sum check.
    let width = 3;
    for av in 0..(1u64 << width) {
        for bv in 0..(1u64 << width) {
            let sum = (av + bv) & mask(width);
            assert!(eval_add_eq(width, av, bv, sum));
            assert!(!eval_add_eq(width, av, bv, (sum + 1) & mask(width)));
        }
    }
}

#[test]
fn differential_extract() {
    // ((_ extract 7 4) x) == y forces the high nibble of x to equal y.
    let script = "
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 4))
        (assert (= ((_ extract 7 4) x) y))
        (assert (= y #b1010))";
    let s = Script::parse(script).unwrap();
    let solver = crate::solver::BvSolver::new(s);
    match solver.solve(100_000).unwrap() {
        crate::solver::BvResult::Sat { model } => {
            let x = model.value_of("x").unwrap().to_u64();
            assert_eq!((x >> 4) & 0xF, 0b1010);
            assert_eq!(model.value_of("y").unwrap().to_u64(), 0b1010);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}
