/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-! ## Boolean circuits

We use a term representation of Boolean circuits, but we measure their size in the
*DAG* sense: the size of a circuit is the number of distinct subcircuits occurring in
it (equivalently, the number of gates when identical subcircuits are shared). -/

/-- Boolean circuits on `n` input variables. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | const : Bool → Circ n
  | not : Circ n → Circ n
  | and : Circ n → Circ n → Circ n
  | or : Circ n → Circ n → Circ n
  deriving DecidableEq

namespace Circ

/-- The Boolean function computed by a circuit. -/

lemma eval_subst {n k : ℕ} (c : Circ k) (σ : Fin k → Circ n) (x : Fin n → Bool) :
    eval (subst c σ) x = eval c (fun i => eval (σ i) x) := by
  induction c with
  | var i => simp [subst, eval]
  | const b => simp [subst, eval]
  | not c ih => simp [subst, eval, ih]
  | and a b iha ihb => simp [subst, eval, iha, ihb]
  | or a b iha ihb => simp [subst, eval, iha, ihb]

