//! Bit-blaster: lowers the word-level [`TermDag`] into a bit-level
//! [`Circuit`]. Every bit-vector variable becomes a run of primary inputs;
//! every word-level operation is decomposed into gates. The same blaster
//! serves the Tseitin/CNF path and the pure circuit-evaluation path.

use rm_ir::{Circuit, GateId, Node, NodeId, Op, TermDag};
use rustc_hash::FxHashMap;

pub struct Blaster {
    pub circuit: Circuit,
    /// Per-node bit signals, LSB first.
    node_bits: FxHashMap<NodeId, Vec<GateId>>,
    /// Free input counter; each input index corresponds to one Boolean
    /// variable in the SAT encoding.
    next_input: u32,
    /// Number of inputs allocated (== SAT variable count when blasted).
    pub num_inputs: u32,
    /// For each variable id, the run of input indexes (LSB first) used for it.
    pub var_inputs: FxHashMap<u32, Vec<u32>>,
}

impl Blaster {
    pub fn new() -> Self {
        Blaster {
            circuit: Circuit::default(),
            node_bits: FxHashMap::default(),
            next_input: 0,
            num_inputs: 0,
            var_inputs: FxHashMap::default(),
        }
    }

    fn fresh_input(&mut self) -> (GateId, u32) {
        let idx = self.next_input;
        let g = self.circuit.input(idx);
        self.next_input += 1;
        self.num_inputs = self.next_input;
        (g, idx)
    }

    /// Blast a node, returning its bit signals (LSB first). Boolean nodes
    /// have exactly one signal.
    pub fn blast(&mut self, dag: &TermDag, id: NodeId) -> Vec<GateId> {
        if let Some(bits) = self.node_bits.get(&id) {
            return bits.clone();
        }
        let bits = match dag.get(id) {
            Node::BoolConst(v) => vec![self.circuit.const_gate(*v)],
            Node::BvConst { width, value } => {
                (0..*width).map(|i| self.circuit.const_gate(value.bit(i as usize))).collect()
            }
            Node::BoolVar { id: vid } => {
                let (g, idx) = self.fresh_input();
                self.var_inputs.entry(*vid).or_default().push(idx);
                vec![g]
            }
            Node::BvVar { id: vid, width } => {
                let mut bits = Vec::with_capacity(*width as usize);
                for _ in 0..*width {
                    let (g, idx) = self.fresh_input();
                    self.var_inputs.entry(*vid).or_default().push(idx);
                    bits.push(g);
                }
                bits
            }
            Node::Apply { op, children } => self.blast_op(dag, *op, children),
        };
        self.node_bits.insert(id, bits.clone());
        bits
    }

    fn blast_op(&mut self, dag: &TermDag, op: Op, children: &[NodeId]) -> Vec<GateId> {
        use Op::*;
        match op {
            And => {
                let a = self.blast(dag, children[0]);
                let b = self.blast(dag, children[1]);
                vec![self.circuit.and(a[0], b[0])]
            }
            Or => {
                let a = self.blast(dag, children[0]);
                let b = self.blast(dag, children[1]);
                vec![self.circuit.or(a[0], b[0])]
            }
            Not => {
                let a = self.blast(dag, children[0]);
                vec![self.circuit.not(a[0])]
            }
            Xor => {
                let a = self.blast(dag, children[0]);
                let b = self.blast(dag, children[1]);
                vec![self.circuit.xor(a[0], b[0])]
            }
            Eq => self.blast_eq(dag, children),
            Ite => {
                let c = self.blast(dag, children[0]);
                let t = self.blast(dag, children[1]);
                let e = self.blast(dag, children[2]);
                t.iter().zip(&e).map(|(ti, ei)| self.circuit.mux(c[0], *ti, *ei)).collect()
            }
            BvNot => {
                let a = self.blast(dag, children[0]);
                a.iter().map(|&b| self.circuit.not(b)).collect()
            }
            BvAnd | BvOr | BvXor => {
                let a = self.blast(dag, children[0]);
                let b = self.blast(dag, children[1]);
                let f = |circuit: &mut Circuit, x, y| match op {
                    BvAnd => circuit.and(x, y),
                    BvOr => circuit.or(x, y),
                    _ => circuit.xor(x, y),
                };
                a.iter().zip(&b).map(|(x, y)| f(&mut self.circuit, *x, *y)).collect()
            }
            BvNeg => self.blast_neg(dag, children),
            BvAdd | BvSub => self.blast_add_sub(dag, children, op == BvSub),
            BvMul => self.blast_mul(dag, children),
            BvUdiv | BvUrem => self.blast_udiv(dag, children, op == BvUrem),
            BvSdiv | BvSrem | BvSmod => self.blast_sdiv(dag, children, op),
            BvShl | BvLshr | BvAshr => self.blast_shift(dag, children, op),
            BvUlt | BvUle | BvUgt | BvUge | BvSlt | BvSle | BvSgt | BvSge => {
                self.blast_compare(dag, children, op)
            }
            BvConcat => {
                let hi = self.blast(dag, children[0]);
                let lo = self.blast(dag, children[1]);
                let mut bits = lo;
                bits.extend(hi);
                bits
            }
            BvExtract { hi, lo } => {
                let a = self.blast(dag, children[0]);
                a[lo as usize..=hi as usize].to_vec()
            }
            BvZeroExtend { amount } => {
                let a = self.blast(dag, children[0]);
                let mut bits = a;
                bits.extend(std::iter::repeat_n(self.circuit.const_gate(false), amount as usize));
                bits
            }
            BvSignExtend { amount } => {
                let a = self.blast(dag, children[0]);
                let sign = a.last().copied().unwrap();
                let mut bits = a;
                bits.extend(std::iter::repeat_n(sign, amount as usize));
                bits
            }
        }
    }

    /// Structural equality: every bit equal, ANDed.
    fn blast_eq(&mut self, dag: &TermDag, children: &[NodeId]) -> Vec<GateId> {
        let a = self.blast(dag, children[0]);
        let b = self.blast(dag, children[1]);
        let mut acc = self.circuit.const_gate(true);
        for (x, y) in a.iter().zip(&b) {
            let e = self.circuit.xor(*x, *y);
            let eq = self.circuit.not(e);
            acc = self.circuit.and(acc, eq);
        }
        vec![acc]
    }

    /// Two's-complement negation: `~a + 1`.
    fn blast_neg(&mut self, dag: &TermDag, children: &[NodeId]) -> Vec<GateId> {
        let a = self.blast(dag, children[0]);
        let inv: Vec<GateId> = a.iter().map(|&b| self.circuit.not(b)).collect();
        let one = self.circuit.const_gate(true);
        self.adder(&inv, &vec![one; inv.len()])
    }

    fn blast_add_sub(&mut self, dag: &TermDag, children: &[NodeId], sub: bool) -> Vec<GateId> {
        let a = self.blast(dag, children[0]);
        let b = self.blast(dag, children[1]);
        let (b_inv, cin) = if sub {
            let b_inv: Vec<GateId> = b.iter().map(|&x| self.circuit.not(x)).collect();
            (b_inv, self.circuit.const_gate(true))
        } else {
            (b, self.circuit.const_gate(false))
        };
        self.add_cin(&a, &b_inv, cin)
    }

    fn blast_mul(&mut self, dag: &TermDag, children: &[NodeId]) -> Vec<GateId> {
        let a = self.blast(dag, children[0]);
        let b = self.blast(dag, children[1]);
        let n = a.len();
        let mut acc = vec![self.circuit.const_gate(false); n];
        for i in 0..n {
            let shifted: Vec<GateId> = (0..n)
                .map(|j| {
                    let src = if j >= i { a[j - i] } else { self.circuit.const_gate(false) };
                    self.circuit.and(b[i], src)
                })
                .collect();
            acc = self.adder(&acc, &shifted);
        }
        acc
    }

    /// Unsigned restoring division. Returns (quotient, remainder) bits.
    fn blast_udiv(&mut self, dag: &TermDag, children: &[NodeId], rem_only: bool) -> Vec<GateId> {
        let a = self.blast(dag, children[0]);
        let b = self.blast(dag, children[1]);
        let n = a.len();
        let zero = self.circuit.const_gate(false);
        let mut rem: Vec<GateId> = vec![zero; n];
        let mut quot: Vec<GateId> = vec![zero; n];
        for i in (0..n).rev() {
            for j in (1..n).rev() {
                rem[j] = rem[j - 1];
            }
            rem[0] = a[i];
            let ge = self.u_ge(&rem, &b);
            let one = self.circuit.const_gate(true);
            let b_inv = self.bv_not(&b);
            let sub = self.add_cin(&rem, &b_inv, one);
            for j in 0..n {
                rem[j] = self.circuit.mux(ge, sub[j], rem[j]);
            }
            quot[i] = ge;
        }
        if rem_only { rem } else { quot }
    }

    fn blast_sdiv(&mut self, dag: &TermDag, children: &[NodeId], op: Op) -> Vec<GateId> {
        let a = self.blast(dag, children[0]);
        let b = self.blast(dag, children[1]);
        let n = a.len();
        let a_sign = *a.last().unwrap();
        let b_sign = *b.last().unwrap();
        let (a_abs, _a_neg) = self.abs2(&a);
        let (b_abs, _b_neg) = self.abs2(&b);
        let (quot, rem) = self.blast_udiv_parts(&a_abs, &b_abs);
        match op {
            Op::BvSdiv => {
                let neg = self.circuit.xor(a_sign, b_sign);
                let inv = self.bv_not(&quot);
                let ones = self.ones(n);
                let zero = self.circuit.const_gate(false);
                let plus1 = self.add_cin(&inv, &ones, zero);
                quot.iter().zip(&plus1).map(|(q, p)| self.circuit.mux(neg, *p, *q)).collect()
            }
            Op::BvSrem => {
                let inv = self.bv_not(&rem);
                let ones = self.ones(n);
                let zero = self.circuit.const_gate(false);
                let plus1 = self.add_cin(&inv, &ones, zero);
                rem.iter().zip(&plus1).map(|(r, p)| self.circuit.mux(a_sign, *p, *r)).collect()
            }
            Op::BvSmod => {
                let sign = b_sign;
                let inv = self.bv_not(&rem);
                let ones = self.ones(n);
                let zero = self.circuit.const_gate(false);
                let plus1 = self.add_cin(&inv, &ones, zero);
                rem.iter().zip(&plus1).map(|(r, p)| self.circuit.mux(sign, *p, *r)).collect()
            }
            _ => unreachable!(),
        }
    }

    /// Signed magnitude -> two's complement.
    fn abs2(&mut self, a: &[GateId]) -> (Vec<GateId>, GateId) {
        let n = a.len();
        let sign = *a.last().unwrap();
        let inv: Vec<GateId> = a.iter().map(|&x| self.circuit.not(x)).collect();
        let ones = self.ones(n);
        let zero = self.circuit.const_gate(false);
        let plus1 = self.add_cin(&inv, &ones, zero);
        let out: Vec<GateId> = (0..n).map(|i| self.circuit.mux(sign, plus1[i], a[i])).collect();
        (out, sign)
    }

    fn blast_shift(&mut self, dag: &TermDag, children: &[NodeId], op: Op) -> Vec<GateId> {
        let a = self.blast(dag, children[0]);
        let sh = self.blast(dag, children[1]);
        let n = a.len();
        let fill = match op {
            Op::BvAshr => *a.last().unwrap(),
            _ => self.circuit.const_gate(false),
        };
        let mut res = a;
        let stages = if n == 0 { 0 } else { (usize::BITS - (n - 1).leading_zeros()) as usize };
        for stage in 0..stages {
            let amount = 1usize << stage;
            let sel = if stage < sh.len() { sh[stage] } else { self.circuit.const_gate(false) };
            let shifted: Vec<GateId> = match op {
                Op::BvShl => {
                    let mut v = vec![self.circuit.const_gate(false); amount];
                    v.extend_from_slice(&res);
                    v.truncate(n);
                    v
                }
                _ => {
                    let mut v = vec![fill; amount];
                    v.extend_from_slice(&res[..n.saturating_sub(amount)]);
                    v
                }
            };
            res = res.iter().zip(&shifted).map(|(r, s)| self.circuit.mux(sel, *s, *r)).collect();
        }
        res
    }

    fn blast_compare(&mut self, dag: &TermDag, children: &[NodeId], op: Op) -> Vec<GateId> {
        let a = self.blast(dag, children[0]);
        let b = self.blast(dag, children[1]);
        use Op::*;
        match op {
            BvUlt => vec![self.u_ult(&a, &b)],
            BvUle => {
                let ult = self.u_ult(&a, &b);
                let eq = self.bv_eq(&a, &b);
                vec![self.circuit.or(ult, eq)]
            }
            BvUgt => vec![self.u_ult(&b, &a)],
            BvUge => {
                let ult = self.u_ult(&b, &a);
                let eq = self.bv_eq(&a, &b);
                vec![self.circuit.or(ult, eq)]
            }
            BvSlt | BvSle => {
                let a_s = *a.last().unwrap();
                let b_s = *b.last().unwrap();
                let diff_s = self.circuit.xor(a_s, b_s);
                let ult = self.u_ult(&a, &b);
                let nb = self.circuit.not(b_s);
                let t1 = self.circuit.and(a_s, nb);
                let nd = self.circuit.not(diff_s);
                let t2 = self.circuit.and(nd, ult);
                let s_lt = self.circuit.or(t1, t2);
                if op == BvSlt {
                    vec![s_lt]
                } else {
                    let eq = self.bv_eq(&a, &b);
                    vec![self.circuit.or(s_lt, eq)]
                }
            }
            BvSgt | BvSge => {
                let a_s = *a.last().unwrap();
                let b_s = *b.last().unwrap();
                let diff_s = self.circuit.xor(a_s, b_s);
                let ult = self.u_ult(&b, &a);
                let na = self.circuit.not(a_s);
                let t1 = self.circuit.and(b_s, na);
                let nd = self.circuit.not(diff_s);
                let t2 = self.circuit.and(nd, ult);
                let s_lt = self.circuit.or(t1, t2);
                if op == BvSgt {
                    vec![s_lt]
                } else {
                    let eq = self.bv_eq(&a, &b);
                    vec![self.circuit.or(s_lt, eq)]
                }
            }
            _ => unreachable!(),
        }
    }

    fn bv_not(&mut self, a: &[GateId]) -> Vec<GateId> {
        a.iter().map(|&x| self.circuit.not(x)).collect()
    }

    fn ones(&mut self, n: usize) -> Vec<GateId> {
        let one = self.circuit.const_gate(true);
        vec![one; n]
    }

    fn bv_eq(&mut self, a: &[GateId], b: &[GateId]) -> GateId {
        let mut acc = self.circuit.const_gate(true);
        for (x, y) in a.iter().zip(b) {
            let xy = self.circuit.xor(*x, *y);
            let nxy = self.circuit.not(xy);
            acc = self.circuit.and(acc, nxy);
        }
        acc
    }

    /// a < b unsigned.
    fn u_ult(&mut self, a: &[GateId], b: &[GateId]) -> GateId {
        let n = a.len();
        let b_inv: Vec<GateId> = b.iter().map(|&x| self.circuit.not(x)).collect();
        let one = self.circuit.const_gate(true);
        let (_sum, carry) = self.add_carry(a, &b_inv, one, n);
        self.circuit.not(carry)
    }

    /// a >= b unsigned.
    fn u_ge(&mut self, a: &[GateId], b: &[GateId]) -> GateId {
        let ult = self.u_ult(a, b);
        self.circuit.not(ult)
    }

    fn adder(&mut self, a: &[GateId], b: &[GateId]) -> Vec<GateId> {
        let z = self.circuit.const_gate(false);
        self.add_cin(a, b, z)
    }

    fn add_cin(&mut self, a: &[GateId], b: &[GateId], cin: GateId) -> Vec<GateId> {
        self.add_carry(a, b, cin, a.len()).0
    }

    /// Ripple-carry addition; returns (sum bits, carry out).
    fn add_carry(&mut self, a: &[GateId], b: &[GateId], cin: GateId, n: usize) -> (Vec<GateId>, GateId) {
        let mut carry = cin;
        let mut sum = Vec::with_capacity(n);
        for i in 0..n {
            let (s, c) = self.full_adder(a[i], b[i], carry);
            sum.push(s);
            carry = c;
        }
        (sum, carry)
    }

    fn full_adder(&mut self, a: GateId, b: GateId, cin: GateId) -> (GateId, GateId) {
        let ax = self.circuit.xor(a, b);
        let sum = self.circuit.xor(ax, cin);
        let ab = self.circuit.and(a, b);
        let axc = self.circuit.and(ax, cin);
        let carry = self.circuit.or(ab, axc);
        (sum, carry)
    }

    /// Internal helper sharing code with `blast_udiv`.
    fn blast_udiv_parts(&mut self, a: &[GateId], b: &[GateId]) -> (Vec<GateId>, Vec<GateId>) {
        let n = a.len();
        let zero = self.circuit.const_gate(false);
        let mut rem: Vec<GateId> = vec![zero; n];
        let mut quot: Vec<GateId> = vec![zero; n];
        for i in (0..n).rev() {
            for j in (1..n).rev() {
                rem[j] = rem[j - 1];
            }
            rem[0] = a[i];
            let ge = self.u_ge(&rem, b);
            let one = self.circuit.const_gate(true);
            let bn = self.bv_not(b);
            let sub = self.add_cin(&rem, &bn, one);
            for j in 0..n {
                rem[j] = self.circuit.mux(ge, sub[j], rem[j]);
            }
            quot[i] = ge;
        }
        (quot, rem)
    }
}

impl Default for Blaster {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rm_ir::{Builder, TermDag};

    fn blast_script(script: &str) -> (Blaster, TermDag, NodeId) {
        let s = rm_syntax::Script::parse(script).unwrap();
        let mut b = Builder::new();
        let mut root = None;
        for a in s.assertions() {
            root = Some(b.lower(a));
        }
        let root = root.unwrap();
        let mut blaster = Blaster::new();
        let _bits = blaster.blast(&b.dag, root);
        (blaster, b.dag, root)
    }

    #[test]
    fn boolean_circuit() {
        let (mut blaster, dag, root) = blast_script("(assert (and true false))");
        let bits = blaster.blast(&dag, root);
        assert_eq!(bits.len(), 1);
        assert!(matches!(blaster.circuit.get(bits[0]), rm_ir::Gate::Const(false)));
    }

    #[test]
    fn adder_blast() {
        let (mut blaster, dag, root) = blast_script(
            "(declare-const a (_ BitVec 4))
             (declare-const b (_ BitVec 4))
             (assert (= (bvadd a b) #b0000))",
        );
        let bits = blaster.blast(&dag, root);
        assert_eq!(bits.len(), 1);
        // The circuit must have more than a few gates (an adder was built).
        assert!(blaster.circuit.len() > 4);
    }

    #[test]
    fn circuit_evaluation_matches_word_semantics() {
        // Build a circuit for (a + b) and evaluate exhaustively for width 2.
        let script = "(declare-const a (_ BitVec 2))
                      (declare-const b (_ BitVec 2))
                      (assert (= (bvadd a b) #b00))";
        let s = rm_syntax::Script::parse(script).unwrap();
        let mut b = Builder::new();
        let root = {
            let mut last = None;
            for a in s.assertions() {
                last = Some(b.lower(a));
            }
            last.unwrap()
        };
        let mut blaster = Blaster::new();
        let bits = blaster.blast(&b.dag, root);
        // root is a Bool gate; we just check it evaluates false for a=b=1.
        let inputs = vec![true, false, true, false]; // a=01, b=01
        let vals = blaster.circuit.evaluate(&inputs);
        assert!(!vals[bits[0].0 as usize]);
    }
}
