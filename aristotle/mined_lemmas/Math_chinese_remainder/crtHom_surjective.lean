/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Function

namespace Math

variable {ι : Type*} [Fintype ι] (n : ι → ℕ)

/-- The canonical ring homomorphism `ZMod (∏ i, n i) →+* Π i, ZMod (n i)`, given componentwise
by reduction modulo `n i`. -/

theorem crtHom_surjective (h : Pairwise (Nat.Coprime on n)) : Function.Surjective (crtHom n) := by
  by_cases hz : ∃ i, n i = 0
  · obtain ⟨i₀, hi₀⟩ := hz
    exact crtHom_surjective_of_zero n h hi₀
  · push_neg at hz
    have : ∀ i, NeZero (n i) := fun i => ⟨hz i⟩
    have hNz : NeZero (∏ i, n i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => hz i⟩
    have hcard : Fintype.card (ZMod (∏ i, n i)) = Fintype.card (∀ i, ZMod (n i)) := by
      rw [ZMod.card, Fintype.card_pi]
      exact Finset.prod_congr rfl fun i _ => (ZMod.card (n i)).symm
    exact ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨crtHom_injective n h, hcard⟩).surjective

end Surjective

