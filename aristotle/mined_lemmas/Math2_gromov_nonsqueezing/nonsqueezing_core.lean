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

theorem nonsqueezing_core {n : ℕ} [NeZero n] {r R : ℝ} (hr : 0 < r)
    (Φ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n) (hΦ : IsLinearSymplectic Φ)
    (hcyl : ∀ v : SymplecticSpace n, ‖v‖ < r → ‖(Φ v) 0‖ < R) : r ≤ R := by
  set e : SymplecticSpace n := EuclideanSpace.single (0 : Fin n) (1 : ℂ) with he
  have hR : 0 < R := by
    have := hcyl 0 (by simpa using hr)
    simpa using this
  set a : SymplecticSpace n := LinearMap.adjoint Φ e with ha
  set b : SymplecticSpace n := LinearMap.adjoint Φ (Complex.I • e) with hb
  have hba : r * ‖a‖ ≤ R := by
    refine norm_le_of_inner_bound hR.le ?_
    intro v hv
    rw [ha, LinearMap.adjoint_inner_left, he, real_inner_single_one_left]
    exact lt_of_le_of_lt (le_trans (le_abs_self _) (Complex.abs_re_le_norm _)) (hcyl v hv)
  have hbb : r * ‖b‖ ≤ R := by
    refine norm_le_of_inner_bound hR.le ?_
    intro v hv
    rw [hb, LinearMap.adjoint_inner_left, he, real_inner_I_single_one_left]
    exact lt_of_le_of_lt (le_trans (le_abs_self _) (Complex.abs_im_le_norm _)) (hcyl v hv)
  have hab : omegaForm a b = 1 := by
    rw [ha, hb, isLinearSymplectic_adjoint hΦ, omegaForm_eq_real_inner,
      real_inner_I_smul_I_smul, real_inner_self_eq_norm_sq, he]
    simp
  have h1 : (1 : ℝ) ≤ ‖a‖ * ‖b‖ := by
    have := abs_omegaForm_le a b
    rw [hab] at this
    simpa using this
  nlinarith [norm_nonneg a, norm_nonneg b]

/-- **Gromov's nonsqueezing theorem, linear case.**
If a linear symplectic transformation of `ℝ^{2n} ≃ ℂ^n` maps the open ball of radius `r`
into the open symplectic cylinder of radius `R` (the cylinder over the first complex
coordinate plane), then `r ≤ R`.  Equivalently, a ball can never be squeezed by a linear
symplectic transformation into a thinner symplectic cylinder, no matter how large the
remaining `2n - 2` directions of the cylinder are. -/
