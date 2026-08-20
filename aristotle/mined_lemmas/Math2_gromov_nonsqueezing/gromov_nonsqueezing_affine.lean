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

theorem gromov_nonsqueezing_affine {n : ℕ} {r R d₁ d₂ : ℝ} (hR : 0 ≤ R)
    (Φ : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (c : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ)
    (hΦ : Φ ∈ Matrix.symplecticGroup (Fin (n + 1)) ℝ)
    (hmaps : ∀ x : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ, x ⬝ᵥ x ≤ r ^ 2 →
      ((Φ *ᵥ x) (Sum.inl 0) + c (Sum.inl 0) - d₁) ^ 2
        + ((Φ *ᵥ x) (Sum.inr 0) + c (Sum.inr 0) - d₂) ^ 2 ≤ R ^ 2) :
    r ≤ R := by
  refine gromov_nonsqueezing hR Φ hΦ ?_
  intro x hx
  have hx' : (-x) ⬝ᵥ (-x) ≤ r ^ 2 := by
    rw [neg_dotProduct, dotProduct_neg, neg_neg]; exact hx
  have h1 := hmaps x hx
  have h2 := hmaps (-x) hx'
  rw [Matrix.mulVec_neg] at h2
  simp only [Pi.neg_apply] at h2
  nlinarith [h1, h2, sq_nonneg (c (Sum.inl 0) - d₁), sq_nonneg (c (Sum.inr 0) - d₂)]

end Math2

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

