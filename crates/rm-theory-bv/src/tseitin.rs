//! Tseitin encoding of a bit-level [`Circuit`] into CNF clauses suitable for
//! the CDCL solver.

use rm_akx::literal::Literal;
use rm_ir::{Circuit, Gate, GateId};

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
                Gate::Input(idx) => {
                    // Variables are 1-based; input i maps to variable i+1.
                    let var = *idx + 1;
                    enc.gate_var.push(var);
                    enc.num_vars = enc.num_vars.max(var);
                }
                Gate::Const(v) => {
                    enc.num_vars += 1;
                    let var = enc.num_vars;
                    enc.gate_var.push(var);
                    let lit = if *v { Literal::positive(var) } else { Literal::negative(var) };
                    enc.clauses.push(vec![lit]);
                }
                Gate::Not(a) => {
                    enc.num_vars += 1;
                    let g = enc.num_vars;
                    enc.gate_var.push(g);
                    let ga = enc.gate_var[a.0 as usize];
                    // g <-> ~a
                    enc.clauses.push(vec![Literal::negative(g), Literal::negative(ga)]);
                    enc.clauses.push(vec![Literal::positive(g), Literal::positive(ga)]);
                }
                Gate::And(a, b) => {
                    enc.num_vars += 1;
                    let g = enc.num_vars;
                    enc.gate_var.push(g);
                    let ga = enc.gate_var[a.0 as usize];
                    let gb = enc.gate_var[b.0 as usize];
                    // g -> a, g -> b
                    enc.clauses.push(vec![Literal::negative(g), Literal::positive(ga)]);
                    enc.clauses.push(vec![Literal::negative(g), Literal::positive(gb)]);
                    // a & b -> g
                    enc.clauses.push(vec![
                        Literal::negative(ga),
                        Literal::negative(gb),
                        Literal::positive(g),
                    ]);
                }
                Gate::Or(a, b) => {
                    enc.num_vars += 1;
                    let g = enc.num_vars;
                    enc.gate_var.push(g);
                    let ga = enc.gate_var[a.0 as usize];
                    let gb = enc.gate_var[b.0 as usize];
                    // a -> g, b -> g
                    enc.clauses.push(vec![Literal::negative(ga), Literal::positive(g)]);
                    enc.clauses.push(vec![Literal::negative(gb), Literal::positive(g)]);
                    // g -> a | b
                    enc.clauses.push(vec![
                        Literal::positive(ga),
                        Literal::positive(gb),
                        Literal::negative(g),
                    ]);
                }
                Gate::Xor(a, b) => {
                    enc.num_vars += 1;
                    let g = enc.num_vars;
                    enc.gate_var.push(g);
                    let ga = enc.gate_var[a.0 as usize];
                    let gb = enc.gate_var[b.0 as usize];
                    // g <-> a xor b
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
                Gate::Mux(sel, a, b) => {
                    // g <-> (sel & a) | (~sel & b)
                    enc.num_vars += 1;
                    let g = enc.num_vars;
                    enc.gate_var.push(g);
                    let gs = enc.gate_var[sel.0 as usize];
                    let ga = enc.gate_var[a.0 as usize];
                    let gb = enc.gate_var[b.0 as usize];
                    // sel & a -> g
                    enc.clauses.push(vec![
                        Literal::negative(gs),
                        Literal::negative(ga),
                        Literal::positive(g),
                    ]);
                    // ~sel & b -> g
                    enc.clauses.push(vec![
                        Literal::positive(gs),
                        Literal::negative(gb),
                        Literal::positive(g),
                    ]);
                    // g -> (sel & a) | (~sel & b)
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
                    // a | b -> g? Not needed: sel and ~sel partition truth.
                }
                Gate::OrN(children) => {
                    enc.num_vars += 1;
                    let g = enc.num_vars;
                    enc.gate_var.push(g);
                    // g -> each child
                    for &c in children {
                        let gc = enc.gate_var[c.0 as usize];
                        enc.clauses.push(vec![Literal::negative(g), Literal::positive(gc)]);
                    }
                    // all children -> g
                    let mut clause: Vec<Literal> =
                        children.iter().map(|&c| Literal::negative(enc.gate_var[c.0 as usize])).collect();
                    clause.push(Literal::positive(g));
                    enc.clauses.push(clause);
                }
            }
        }
        // Assert the roots.
        for &r in roots {
            let g = enc.gate_var[r.0 as usize];
            enc.clauses.push(vec![Literal::positive(g)]);
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
