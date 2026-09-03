//! Bit-level Boolean circuit IR: a gate netlist with AIG-style combinators
//! plus evaluation. This is the representation GPU kernels (M5) evaluate over
//! batches and that bit-blasting can build on.

use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize, Deserialize)]
pub struct GateId(pub u32);

/// A single gate in the netlist. `children` reference earlier gates.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Gate {
    Const(bool),
    /// Primary input; the index into the evaluation input vector.
    Input(u32),
    Not(GateId),
    And(GateId, GateId),
    Or(GateId, GateId),
    Xor(GateId, GateId),
    /// Multiplexer: `(sel ? a : b)`.
    Mux(GateId, GateId, GateId),
    /// True when any child is true (variadic or).
    OrN(Vec<GateId>),
}

/// A circuit netlist. Gates are added in topological order, so evaluation is
/// a single forward pass.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Circuit {
    gates: Vec<Gate>,
}

impl Circuit {
    pub fn len(&self) -> usize {
        self.gates.len()
    }
    pub fn is_empty(&self) -> bool {
        self.gates.is_empty()
    }

    pub fn get(&self, id: GateId) -> &Gate {
        &self.gates[id.0 as usize]
    }

    pub fn gates(&self) -> &[Gate] {
        &self.gates
    }

    fn add(&mut self, gate: Gate) -> GateId {
        let id = GateId(self.gates.len() as u32);
        self.gates.push(gate);
        id
    }

    pub fn const_gate(&mut self, v: bool) -> GateId {
        self.add(Gate::Const(v))
    }

    pub fn input(&mut self, idx: u32) -> GateId {
        self.add(Gate::Input(idx))
    }

    pub fn not(&mut self, a: GateId) -> GateId {
        if let Gate::Const(v) = self.get(a) {
            return self.const_gate(!v);
        }
        self.add(Gate::Not(a))
    }

    pub fn and(&mut self, a: GateId, b: GateId) -> GateId {
        let a_false = matches!(self.get(a), Gate::Const(false));
        let b_false = matches!(self.get(b), Gate::Const(false));
        let a_true = matches!(self.get(a), Gate::Const(true));
        let b_true = matches!(self.get(b), Gate::Const(true));
        if a_false || b_false {
            return self.const_gate(false);
        }
        if a_true {
            return b;
        }
        if b_true {
            return a;
        }
        self.add(Gate::And(a, b))
    }

    pub fn or(&mut self, a: GateId, b: GateId) -> GateId {
        let a_true = matches!(self.get(a), Gate::Const(true));
        let b_true = matches!(self.get(b), Gate::Const(true));
        let a_false = matches!(self.get(a), Gate::Const(false));
        let b_false = matches!(self.get(b), Gate::Const(false));
        if a_true || b_true {
            return self.const_gate(true);
        }
        if a_false {
            return b;
        }
        if b_false {
            return a;
        }
        self.add(Gate::Or(a, b))
    }

    pub fn or_n(&mut self, children: Vec<GateId>) -> GateId {
        if children.is_empty() {
            return self.const_gate(false);
        }
        if children
            .iter()
            .any(|&c| matches!(self.get(c), Gate::Const(true)))
        {
            return self.const_gate(true);
        }
        let filtered: Vec<GateId> = children
            .into_iter()
            .filter(|&c| !matches!(self.get(c), Gate::Const(false)))
            .collect();
        match filtered.len() {
            0 => self.const_gate(false),
            1 => filtered[0],
            _ => self.add(Gate::OrN(filtered)),
        }
    }

    pub fn xor(&mut self, a: GateId, b: GateId) -> GateId {
        let a_f = matches!(self.get(a), Gate::Const(false));
        let b_f = matches!(self.get(b), Gate::Const(false));
        let a_t = matches!(self.get(a), Gate::Const(true));
        let b_t = matches!(self.get(b), Gate::Const(true));
        if a_f {
            return b;
        }
        if b_f {
            return a;
        }
        if a_t {
            return self.not(b);
        }
        if b_t {
            return self.not(a);
        }
        self.add(Gate::Xor(a, b))
    }

    pub fn mux(&mut self, sel: GateId, a: GateId, b: GateId) -> GateId {
        let sel_a = self.and(sel, a);
        let nsel = self.not(sel);
        let nsel_b = self.and(nsel, b);
        self.or(sel_a, nsel_b)
    }

    /// Evaluate the whole circuit for one input assignment; returns the
    /// value of every gate. `inputs[i]` is the value of input i.
    pub fn evaluate(&self, inputs: &[bool]) -> Vec<bool> {
        let mut vals = vec![false; self.gates.len()];
        for (i, gate) in self.gates.iter().enumerate() {
            let v = match gate {
                Gate::Const(v) => *v,
                Gate::Input(idx) => inputs[*idx as usize],
                Gate::Not(a) => !vals[a.0 as usize],
                Gate::And(a, b) => vals[a.0 as usize] && vals[b.0 as usize],
                Gate::Or(a, b) => vals[a.0 as usize] || vals[b.0 as usize],
                Gate::Xor(a, b) => vals[a.0 as usize] ^ vals[b.0 as usize],
                Gate::Mux(sel, a, b) => {
                    if vals[sel.0 as usize] {
                        vals[a.0 as usize]
                    } else {
                        vals[b.0 as usize]
                    }
                }
                Gate::OrN(children) => children.iter().any(|&c| vals[c.0 as usize]),
            };
            vals[i] = v;
        }
        vals
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn netlist_evaluation() {
        let mut c = Circuit::default();
        let x = c.input(0);
        let y = c.input(1);
        let n = c.not(x);
        let both = c.and(x, y);
        let out = c.or(n, both);
        assert!(c.evaluate(&[false, false])[out.0 as usize]);
        assert!(!c.evaluate(&[true, false])[out.0 as usize]);
        assert!(c.evaluate(&[true, true])[out.0 as usize]);
    }

    #[test]
    fn constant_folding() {
        let mut c = Circuit::default();
        let t = c.const_gate(true);
        let f = c.const_gate(false);
        let x = c.input(0);
        let axf = c.and(x, f);
        assert!(matches!(c.get(axf), Gate::Const(false)));
        let axt = c.and(x, t);
        assert_eq!(axt, x);
        let oxf = c.or(x, t);
        assert!(matches!(c.get(oxf), Gate::Const(true)));
        let xxf = c.xor(x, f);
        assert_eq!(xxf, x);
    }

    #[test]
    fn mux_behavior() {
        let mut c = Circuit::default();
        let sel = c.input(0);
        let a = c.input(1);
        let b = c.input(2);
        let out = c.mux(sel, a, b);
        assert!(c.evaluate(&[true, true, false])[out.0 as usize]);
        assert!(!c.evaluate(&[true, false, true])[out.0 as usize]);
        assert!(c.evaluate(&[false, false, true])[out.0 as usize]);
        assert!(!c.evaluate(&[false, true, false])[out.0 as usize]);
    }
}
