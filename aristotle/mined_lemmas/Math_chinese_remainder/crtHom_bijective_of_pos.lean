import Mathlib

/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Function

namespace Math

variable {ι : Type*} [Fintype ι]

/-- The natural reduction ring homomorphism `ℤ/(∏ i, n i) → ∏ i, ℤ/(n i)`. -/

lemma crtHom_bijective_of_pos (n : ι → ℕ) (hco : Pairwise (Nat.Coprime on n))
    (hpos : ∀ i, 0 < n i) : Function.Bijective (crtHom n) := by
  classical
  haveI : ∀ i, NeZero (n i) := fun i => ⟨(hpos i).ne'⟩
  haveI : NeZero (∏ i, n i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne'⟩
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨crtHom_injective n hco, ?_⟩
  rw [ZMod.card, Fintype.card_pi]
  exact Finset.prod_congr rfl fun i _ => (ZMod.card (n i)).symm

omit [Fintype ι] in
/-- If one modulus is zero, evaluation at that index is a bijection of `∏ i, ℤ/(n i)`
onto `ℤ/(n i₀)`, since all other moduli are then `1`. -/
