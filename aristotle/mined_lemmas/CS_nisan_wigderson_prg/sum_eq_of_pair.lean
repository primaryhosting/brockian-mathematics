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

lemma sum_eq_of_pair {β : Type*} [Fintype β] (T : β → β) (hT : Function.Involutive T)
    (F W : β → ℝ) (h : ∀ b, F b + F (T b) = W b + W (T b)) :
    ∑ b, F b = ∑ b, W b := by
  have h1 : ∑ b, F (T b) = ∑ b, F b := Equiv.sum_comp (hT.toPerm T) F
  have h2 : ∑ b, W (T b) = ∑ b, W b := Equiv.sum_comp (hT.toPerm T) W
  have h3 : ∑ b, (F b + F (T b)) = ∑ b, (W b + W (T b)) :=
    Finset.sum_congr rfl (fun b _ => h b)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2] at h3
  linarith

/-- The heart of the Nisan-Wigderson analysis: consecutive hybrids are close, since a
distinguisher between them yields a small circuit predicting the hard function. -/
