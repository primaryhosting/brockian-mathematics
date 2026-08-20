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

lemma hybAcc_top {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (D : Circ m) :
    hybAcc e f D m = (∑ z : Fin d → Bool, b2r (D.eval (fun i => f (z ∘ e i)))) / 2 ^ d := by
  have h : ∀ z : Fin d → Bool,
      (∑ _y : Fin m → Bool, b2r (D.eval (fun j => if (j : ℕ) < m then f (z ∘ e j) else _y j)))
        = (2 : ℝ) ^ m * b2r (D.eval (fun j => f (z ∘ e j))) := by
    intro z
    have hcm : ((Fintype.card (Fin m → Bool) : ℕ) : ℝ) = 2 ^ m := by simp
    have : ∀ y : Fin m → Bool,
        b2r (D.eval (fun j => if (j : ℕ) < m then f (z ∘ e j) else y j))
          = b2r (D.eval (fun j => f (z ∘ e j))) := by
      intro y
      congr 1
      congr 1
      funext j
      simp [j.isLt]
    rw [Finset.sum_congr rfl (fun y _ => this y), Finset.sum_const]
    simp only [Finset.card_univ, nsmul_eq_mul, hcm]
  rw [hybAcc, Finset.sum_congr rfl (fun z _ => h z), ← Finset.mul_sum]
  rw [mul_comm ((2:ℝ) ^ d) ((2:ℝ) ^ m), mul_div_mul_left _ _ (by positivity)]

/-- The difference of two consecutive hybrids, written in terms of the next-bit strings. -/
