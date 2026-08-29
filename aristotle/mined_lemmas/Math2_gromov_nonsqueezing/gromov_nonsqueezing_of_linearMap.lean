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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

open Complex

/-- The standard symplectic vector space `ℝ^{2(n+1)}`, modelled as `ℂ^{n+1}` viewed as a
real vector space. -/
abbrev SympSpace (n : ℕ) : Type := EuclideanSpace ℂ (Fin (n + 1))

/-- The standard symplectic form on `ℂ^{n+1} ≅ ℝ^{2(n+1)}`:
`ω(z, w) = Im ⟪z, w⟫ = ∑ᵢ (xᵢ y'ᵢ - yᵢ x'ᵢ)`. -/

theorem gromov_nonsqueezing_of_linearMap {n : ℕ} {r R : ℝ} (hr : 0 < r)
    (Φ : SympSpace n →ₗ[ℝ] SympSpace n)
    (hΦ : ∀ z w : SympSpace n, omegaForm (Φ z) (Φ w) = omegaForm z w)
    (hsq : ∀ z : SympSpace n, ‖z‖ < r → ‖(Φ z) 0‖ < R) : r ≤ R := by
  have hnd : ∀ z : SympSpace n, omegaForm z (Complex.I • z) = ‖z‖ ^ 2 := by
    intro z
    rw [omegaForm, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp
    norm_cast
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    have h := hΦ z (Complex.I • z)
    rw [hz, hnd z] at h
    simp [omegaForm] at h
    have hz0 : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
    exact norm_eq_zero.mp hz0
  have hbij : Function.Bijective Φ := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact gromov_nonsqueezing hr (LinearEquiv.ofBijective Φ hbij) (fun z w => hΦ z w) hsq

end Math2

