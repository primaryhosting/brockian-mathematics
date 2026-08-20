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

lemma adjoint_I_smul_apply {n : ℕ} {Φ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n}
    (hΦ : IsLinearSymplectic Φ) (u : SymplecticSpace n) :
    LinearMap.adjoint Φ (Complex.I • Φ u) = Complex.I • u := by
  have key : ∀ v : SymplecticSpace n,
      ⟪LinearMap.adjoint Φ (Complex.I • Φ u), v⟫_ℝ = ⟪Complex.I • u, v⟫_ℝ := by
    intro v
    rw [LinearMap.adjoint_inner_left, ← omegaForm_eq_real_inner, ← omegaForm_eq_real_inner, hΦ]
  have h2 : LinearMap.adjoint Φ (Complex.I • Φ u) - Complex.I • u = 0 := by
    rw [← @inner_self_eq_zero ℝ, inner_sub_left, key, sub_self]
  exact sub_eq_zero.mp h2

