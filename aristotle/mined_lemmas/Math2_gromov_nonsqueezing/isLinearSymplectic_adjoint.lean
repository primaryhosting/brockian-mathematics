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
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

noncomputable section

/-- The standard symplectic vector space `ℝ^{2n} ≃ ℂ^n`, equipped with its Euclidean
structure.  The standard symplectic form is the imaginary part of the Hermitian inner
product. -/
abbrev SymplecticSpace (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The standard symplectic form on `ℂ^n ≃ ℝ^{2n}`:
`ω(z, w) = Im ⟪z, w⟫ = ∑ i, (x i * v i - y i * u i)`, where `z i = x i + I * y i` and
`w i = u i + I * v i`. -/

lemma isLinearSymplectic_adjoint {n : ℕ} {Φ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n}
    (hΦ : IsLinearSymplectic Φ) : IsLinearSymplectic (LinearMap.adjoint Φ) := by
  intro u v
  obtain ⟨p, hp⟩ := symplectic_surjective hΦ (-(Complex.I • u))
  obtain ⟨q, hq⟩ := symplectic_surjective hΦ (-(Complex.I • v))
  have hu : Complex.I • Φ p = u := by rw [hp, smul_neg, I_smul_I_smul, neg_neg]
  have hv : Complex.I • Φ q = v := by rw [hq, smul_neg, I_smul_I_smul, neg_neg]
  have hau : LinearMap.adjoint Φ u = Complex.I • p := by rw [← hu, adjoint_I_smul_apply hΦ]
  have hav : LinearMap.adjoint Φ v = Complex.I • q := by rw [← hv, adjoint_I_smul_apply hΦ]
  rw [hau, hav, omegaForm_eq_real_inner, I_smul_I_smul, inner_neg_left, ← real_inner_I_smul_left,
    ← omegaForm_eq_real_inner, ← hΦ p q, hp, hq, omegaForm_eq_real_inner, smul_neg,
    I_smul_I_smul, neg_neg, inner_neg_right, ← real_inner_I_smul_left,
    ← omegaForm_eq_real_inner]

/-! ### Coordinate functionals -/

