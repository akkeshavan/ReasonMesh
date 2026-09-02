//! End-to-end QF_BV solver: SMT-LIB script -> AST -> term DAG -> bit-blast ->
//! Tseitin CNF -> CDCL. Model values are reported per declared variable.

use crate::blaster::Blaster;
use crate::tseitin::EncodedCnf;
use rm_ir::{Bv, Builder, GateId, NodeId};
use rm_sat::{CdclSolver, SolveResult};
use rm_syntax::{Command, Script};
use rustc_hash::FxHashMap;

/// Outcome of a QF_BV solve.
#[derive(Clone, Debug)]
pub enum BvResult {
    Sat { model: BvModel },
    Unsat,
    Unknown,
}

/// A satisfying assignment: declared variable name -> bit-vector value.
#[derive(Clone, Debug, Default)]
pub struct BvModel {
    /// name -> value
    pub values: FxHashMap<String, Bv>,
}

impl BvModel {
    pub fn value_of(&self, name: &str) -> Option<&Bv> {
        self.values.get(name)
    }
}

/// A solver for a single QF_BV script.
pub struct BvSolver {
    script: Script,
}

impl BvSolver {
    pub fn new(script: Script) -> Self {
        BvSolver { script }
    }

    /// The set of declared constant variables (name -> width).
    pub fn declared(&self) -> Vec<(String, u32)> {
        let mut out = Vec::new();
        for cmd in &self.script.commands {
            if let Command::DeclareFun { name, args, result } = cmd {
                if args.is_empty() {
                    if let Some(w) = result.as_bitvec() {
                        out.push((name.clone(), w));
                    }
                }
            }
        }
        out
    }

    /// Solve the assertions in the script.
    pub fn solve(&self, max_conflicts: u64) -> Result<BvResult, String> {
        let mut builder = Builder::new();
        let mut roots: Vec<NodeId> = Vec::new();
        for a in self.script.assertions() {
            roots.push(builder.lower(a));
        }

        // Encode: blast roots, Tseitin into CNF.
        let mut blaster = Blaster::new();
        let mut root_bits: Vec<GateId> = Vec::new();
        for &r in &roots {
            root_bits.extend(blaster.blast(&builder.dag, r));
        }
        let cnf = EncodedCnf::encode(&blaster.circuit, &root_bits);

        let mut solver = CdclSolver::new(cnf.num_vars);
        for clause in &cnf.clauses {
            solver.add_clause(clause);
        }
        match solver.solve(&[], max_conflicts) {
            SolveResult::Sat(model) => {
                // Map declared variables to values: name -> var id -> inputs.
                let mut values = FxHashMap::default();
                for (name, width) in self.declared() {
                    let Some(vid) = builder.var_id(&name) else { continue };
                    let Some(inputs) = blaster.var_inputs.get(&vid) else { continue };
                    let bits: Vec<bool> = inputs.iter().map(|&i| model.value_of(i + 1)).collect();
                    let mut bv_bits = vec![false; width as usize];
                    for (j, &b) in bits.iter().enumerate() {
                        if j < width as usize {
                            bv_bits[j] = b;
                        }
                    }
                    values.insert(name.clone(), Bv::from_bits(width, bv_bits));
                }
                Ok(BvResult::Sat { model: BvModel { values } })
            }
            SolveResult::Unsat => Ok(BvResult::Unsat),
            SolveResult::Unknown => Ok(BvResult::Unknown),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve(script: &str) -> BvResult {
        let s = Script::parse(script).unwrap();
        BvSolver::new(s).solve(100_000).unwrap()
    }

    #[test]
    fn trivially_sat() {
        assert!(matches!(solve("(declare-const x (_ BitVec 8)) (assert true)"), BvResult::Sat { .. }));
    }

    #[test]
    fn contradiction_unsat() {
        assert!(matches!(
            solve("(declare-const x (_ BitVec 8)) (assert (= x #x00)) (assert (= x #x01))"),
            BvResult::Unsat
        ));
    }

    #[test]
    fn equality_sat() {
        let r = solve("(declare-const x (_ BitVec 8)) (assert (= x #x2A))");
        match r {
            BvResult::Sat { model } => {
                assert_eq!(model.value_of("x").unwrap().to_u64(), 0x2A);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn addition_model_is_consistent() {
        // (a + b) & 0xF == 5 is satisfiable with a concrete solution.
        let r = solve(
            "(declare-const a (_ BitVec 4))
             (declare-const b (_ BitVec 4))
             (assert (= (bvadd a b) #b0101))",
        );
        match r {
            BvResult::Sat { model } => {
                let a = model.value_of("a").unwrap().to_u64();
                let b = model.value_of("b").unwrap().to_u64();
                assert_eq!((a + b) & 0xF, 5);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn addition_can_be_unsat() {
        // a + a == 1 mod 2 is unsat (2a is always even).
        assert!(matches!(
            solve("(declare-const a (_ BitVec 4)) (assert (= (bvadd a a) #b0001))"),
            BvResult::Unsat
        ));
    }

    #[test]
    fn comparison_sat_and_model() {
        let r = solve(
            "(declare-const a (_ BitVec 8))
             (assert (bvult a #x0A))",
        );
        match r {
            BvResult::Sat { model } => {
                assert!(model.value_of("a").unwrap().to_u64() < 10);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn xor_and_mul_roundtrip() {
        let r = solve(
            "(declare-const a (_ BitVec 4))
             (assert (= (bvmul a a) (bvxor a #b0011)))",
        );
        // a*a == a xor 3 over 4 bits: try a=1 -> 1 vs 2, a=3 -> 9 mod 16 = 9
        // vs 0, ... Only satisfiable if some a works; it turns out a=5 works
        // (25 mod 16 = 9, 5 xor 3 = 6 — no). a=7: 49 mod 16 = 1, 7 xor 3 = 4.
        // So this instance is genuinely UNSAT; assert that the solver says so.
        assert!(matches!(r, BvResult::Unsat));
    }

    #[test]
    fn mul_model_satisfies() {
        let r = solve(
            "(declare-const a (_ BitVec 4))
             (assert (= (bvmul a #b0011) #b0100))",
        );
        // 3a == 4 mod 16 -> a = 4 * 3^{-1}; gcd(3,16)=1 so 3^{-1}=11 (33 mod
        // 16 = 1), a = 44 mod 16 = 12. Check the model.
        match r {
            BvResult::Sat { model } => {
                let a = model.value_of("a").unwrap().to_u64();
                assert_eq!((a * 3) & 0xF, 4);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn extract_and_concat() {
        let r = solve(
            "(declare-const x (_ BitVec 8))
             (assert (= ((_ extract 7 4) x) #b1010))
             (assert (= ((_ extract 3 0) x) #b0011))",
        );
        match r {
            BvResult::Sat { model } => {
                let v = model.value_of("x").unwrap().to_u64();
                assert_eq!((v >> 4) & 0xF, 0b1010);
                assert_eq!(v & 0xF, 0b0011);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn sign_extend_preserves_negative() {
        let r = solve(
            "(declare-const x (_ BitVec 4))
             (assert (= ((_ sign_extend 4) x) ((_ zero_extend 4) x)))",
        );
        // Equality of sign- and zero-extension only holds when the sign bit
        // is zero, i.e. x is non-negative. Always satisfiable.
        match r {
            BvResult::Sat { model } => {
                let x = model.value_of("x").unwrap().to_u64();
                assert!(x < 8);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn shift_ult_is_sat() {
        let r = solve(
            "(declare-const a (_ BitVec 4))
             (declare-const b (_ BitVec 4))
             (assert (bvult (bvshl a b) #b0100))",
        );
        assert!(matches!(r, BvResult::Sat { .. }));
    }

    #[test]
    fn ite_selects_correct_branch() {
        let r = solve(
            "(declare-const c Bool)
             (declare-const a (_ BitVec 8))
             (declare-const b (_ BitVec 8))
             (assert (ite c (= a #x01) (= a #x02)))
             (assert c)",
        );
        match r {
            BvResult::Sat { model } => {
                assert_eq!(model.value_of("a").unwrap().to_u64(), 1);
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }

    #[test]
    fn distinct_variables() {
        let r = solve(
            "(declare-const a (_ BitVec 8))
             (declare-const b (_ BitVec 8))
             (assert (distinct a b))",
        );
        match r {
            BvResult::Sat { model } => {
                assert_ne!(
                    model.value_of("a").unwrap().to_u64(),
                    model.value_of("b").unwrap().to_u64()
                );
            }
            other => panic!("expected Sat, got {other:?}"),
        }
    }
}
