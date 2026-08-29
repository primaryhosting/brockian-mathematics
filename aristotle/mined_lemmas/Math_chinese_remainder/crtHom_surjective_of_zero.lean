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

private lemma crtHom_surjective_of_zero (h : Pairwise (Nat.Coprime on n)) {i₀ : ι}
    (hi₀ : n i₀ = 0) : Function.Surjective (crtHom n) := by
  have hone : ∀ j, j ≠ i₀ → n j = 1 := by
    intro j hj
    have := h (Ne.symm hj)
    rw [Function.onFun, hi₀, Nat.coprime_zero_left] at this
    exact this
  have hN : ∏ i, n i = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀) hi₀
  intro f
  refine ⟨ZMod.ringEquivCongr (hi₀.trans hN.symm) (f i₀), ?_⟩
  funext j
  by_cases hj : j = i₀
  · subst hj
    exact castHom_ringEquivCongr _ _ _
  · have : Subsingleton (ZMod (n j)) := by
      rw [hone j hj]; infer_instance
    exact Subsingleton.elim _ _

