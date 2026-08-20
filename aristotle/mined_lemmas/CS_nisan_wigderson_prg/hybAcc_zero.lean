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

lemma hybAcc_zero {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (D : Circ m) :
    hybAcc e f D 0 = (∑ y : Fin m → Bool, b2r (D.eval y)) / 2 ^ m := by
  have h : ∀ z : Fin d → Bool,
      (∑ y : Fin m → Bool, b2r (D.eval (fun j => if (j : ℕ) < 0 then f (z ∘ e j) else y j)))
        = ∑ y : Fin m → Bool, b2r (D.eval y) := by
    intro z; simp
  have hc : ((Fintype.card (Fin d → Bool) : ℕ) : ℝ) = 2 ^ d := by simp
  rw [hybAcc, Finset.sum_congr rfl (fun z _ => h z), Finset.sum_const]
  simp only [Finset.card_univ, nsmul_eq_mul, hc]
  exact mul_div_mul_left _ _ (by positivity)

