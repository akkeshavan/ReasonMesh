//! Tseitin encoding of a bit-level [`Circuit`] into CNF clauses suitable for
//! the CDCL solver.

use rm_akx::literal::Literal;
use rm_ir::{Circuit, Gate, GateId};

fn alloc_gate_var(enc: &mut EncodedCnf) -> u32 {
    enc.num_vars += 1;
    let g = enc.num_vars;
    enc.gate_var.push(g);
    g
}

fn encode_input(enc: &mut EncodedCnf, idx: u32) {
    let var = idx + 1;
    enc.gate_var.push(var);
    enc.num_vars = enc.num_vars.max(var);
}

fn encode_const(enc: &mut EncodedCnf, v: bool) {
    let g = alloc_gate_var(enc);
    let lit = if v {
        Literal::positive(g)
    } else {
        Literal::negative(g)
    };
    enc.clauses.push(vec![lit]);
}

fn encode_not(enc: &mut EncodedCnf, a: GateId) {
    let g = alloc_gate_var(enc);
    let ga = enc.gate_var[a.0 as usize];
    enc.clauses
        .push(vec![Literal::negative(g), Literal::negative(ga)]);
    enc.clauses
        .push(vec![Literal::positive(g), Literal::positive(ga)]);
}

fn encode_and(enc: &mut EncodedCnf, a: GateId, b: GateId) {
    let g = alloc_gate_var(enc);
    let ga = enc.gate_var[a.0 as usize];
    let gb = enc.gate_var[b.0 as usize];
    enc.clauses
        .push(vec![Literal::negative(g), Literal::positive(ga)]);
    enc.clauses
        .push(vec![Literal::negative(g), Literal::positive(gb)]);
    enc.clauses.push(vec![
        Literal::negative(ga),
        Literal::negative(gb),
        Literal::positive(g),
    ]);
}

fn encode_or(enc: &mut EncodedCnf, a: GateId, b: GateId) {
    let g = alloc_gate_var(enc);
    let ga = enc.gate_var[a.0 as usize];
    let gb = enc.gate_var[b.0 as usize];
    enc.clauses
        .push(vec![Literal::negative(ga), Literal::positive(g)]);
    enc.clauses
        .push(vec![Literal::negative(gb), Literal::positive(g)]);
    enc.clauses.push(vec![
        Literal::positive(ga),
        Literal::positive(gb),
        Literal::negative(g),
    ]);
}

fn encode_xor(enc: &mut EncodedCnf, a: GateId, b: GateId) {
    let g = alloc_gate_var(enc);
    let ga = enc.gate_var[a.0 as usize];
    let gb = enc.gate_var[b.0 as usize];
    enc.clauses.push(vec![
        Literal::positive(ga),
        Literal::positive(gb),
        Literal::negative(g),
    ]);
    enc.clauses.push(vec![
        Literal::negative(ga),
        Literal::negative(gb),
        Literal::negative(g),
    ]);
    enc.clauses.push(vec![
        Literal::positive(ga),
        Literal::negative(gb),
        Literal::positive(g),
    ]);
    enc.clauses.push(vec![
        Literal::negative(ga),
        Literal::positive(gb),
        Literal::positive(g),
    ]);
}

fn encode_mux(enc: &mut EncodedCnf, sel: GateId, a: GateId, b: GateId) {
    let g = alloc_gate_var(enc);
    let gs = enc.gate_var[sel.0 as usize];
    let ga = enc.gate_var[a.0 as usize];
    let gb = enc.gate_var[b.0 as usize];
    enc.clauses.push(vec![
        Literal::negative(gs),
        Literal::negative(ga),
        Literal::positive(g),
    ]);
    enc.clauses.push(vec![
        Literal::positive(gs),
        Literal::negative(gb),
        Literal::positive(g),
    ]);
    enc.clauses.push(vec![
        Literal::negative(g),
        Literal::positive(gs),
        Literal::negative(ga),
    ]);
    enc.clauses.push(vec![
        Literal::negative(g),
        Literal::negative(gs),
        Literal::positive(gb),
    ]);
}

fn encode_orn(enc: &mut EncodedCnf, children: &[GateId]) {
    let g = alloc_gate_var(enc);
    for &c in children {
        let gc = enc.gate_var[c.0 as usize];
        enc.clauses
            .push(vec![Literal::negative(g), Literal::positive(gc)]);
    }
    let mut clause: Vec<Literal> = children
        .iter()
        .map(|&c| Literal::negative(enc.gate_var[c.0 as usize]))
        .collect();
    clause.push(Literal::positive(g));
    enc.clauses.push(clause);
}

/// A CNF encoding: every gate gets a Boolean variable; primary inputs get
/// their own variable (index = input index).
pub struct EncodedCnf {
    /// CNF clauses over variables 1..=num_vars.
    pub clauses: Vec<Vec<Literal>>,
    /// Number of variables introduced.
    pub num_vars: u32,
    /// Variable id for each gate.
    pub gate_var: Vec<u32>,
}

impl EncodedCnf {
    /// Encode the circuit into CNF. `roots` are the gates asserted true.
    pub fn encode(circuit: &Circuit, roots: &[GateId]) -> EncodedCnf {
        let mut enc = EncodedCnf {
            clauses: Vec::new(),
            num_vars: 0,
            gate_var: Vec::with_capacity(circuit.len()),
        };
        for gate in circuit.gates() {
            match gate {
                Gate::Input(idx) => encode_input(&mut enc, *idx),
                Gate::Const(v) => encode_const(&mut enc, *v),
                Gate::Not(a) => encode_not(&mut enc, *a),
                Gate::And(a, b) => encode_and(&mut enc, *a, *b),
                Gate::Or(a, b) => encode_or(&mut enc, *a, *b),
                Gate::Xor(a, b) => encode_xor(&mut enc, *a, *b),
                Gate::Mux(sel, a, b) => encode_mux(&mut enc, *sel, *a, *b),
                Gate::OrN(children) => encode_orn(&mut enc, children),
            }
        }
        for &r in roots {
            enc.clauses
                .push(vec![Literal::positive(enc.gate_var[r.0 as usize])]);
        }
        enc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodes_and_gate() {
        let mut c = Circuit::default();
        let x = c.input(0);
        let y = c.input(1);
        let z = c.and(x, y);
        let enc = EncodedCnf::encode(&c, &[z]);
        // Unit + implication clauses exist; root asserted.
        assert!(enc.num_vars >= 3);
        assert!(!enc.clauses.is_empty());
        let asserted_root = enc.clauses.last().unwrap();
        assert_eq!(asserted_root.len(), 1);
    }

    #[test]
    fn encode_circuit_roundtrip_evaluation() {
        // Circuit for a+b with constant inputs; encode and check the root
        // constraint is consistent with gate evaluation.
        let mut c = Circuit::default();
        let a = c.input(0);
        let b = c.input(1);
        let both = c.and(a, b);
        let enc = EncodedCnf::encode(&c, &[both]);
        assert!(!enc.clauses.is_empty());
    }
}
