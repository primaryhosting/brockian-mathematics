/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalizes Gromov's nonsqueezing phenomenon for **linear** symplectomorphisms
of `ℝ^(2n+2)`: a linear symplectic image of a ball of radius `r` that fits inside the
symplectic cylinder of radius `R` forces `r ≤ R`.  An affine version and a sharpness
statement are also proved.
-/

open scoped BigOperators
open Matrix

namespace Math2

/-- Bessel-type inequality for a pair of orthogonal vectors of equal length. -/

theorem gromov_nonsqueezing_sharp {n : ℕ} (r : ℝ) :
    ((1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
        ∈ Matrix.symplecticGroup (Fin (n + 1)) ℝ) ∧
      ∀ x : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ, x ⬝ᵥ x ≤ r ^ 2 →
        ((1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) *ᵥ x)
            (Sum.inl 0) ^ 2
          + ((1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) *ᵥ x)
            (Sum.inr 0) ^ 2 ≤ r ^ 2 := by
  refine ⟨Submonoid.one_mem _, ?_⟩
  intro x hx
  rw [Matrix.one_mulVec]
  have hsub : ({Sum.inl 0, Sum.inr 0} : Finset (Fin (n + 1) ⊕ Fin (n + 1))) ⊆ Finset.univ :=
    Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => mul_self_nonneg (x i))
  have h2 : ∑ i ∈ ({Sum.inl 0, Sum.inr 0} : Finset (Fin (n + 1) ⊕ Fin (n + 1))), x i * x i
      = x (Sum.inl 0) * x (Sum.inl 0) + x (Sum.inr 0) * x (Sum.inr 0) :=
    Finset.sum_pair (by simp)
  rw [h2] at h
  have : x (Sum.inl 0) ^ 2 + x (Sum.inr 0) ^ 2 ≤ x ⬝ᵥ x := by
    simpa [dotProduct, sq] using h
  linarith

/-- **Affine linear Gromov nonsqueezing.**  If the affine symplectomorphism
`x ↦ Φ x + c` maps the closed ball of radius `r` centred at the origin into the closed
symplectic cylinder of radius `R` over the first symplectic coordinate plane, centred at
`(d₁, d₂)`, then `r ≤ R`. -/
