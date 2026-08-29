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

lemma one_le_norm_pVec_mul_norm_qVec : 1 ≤ ‖pVec Φ‖ * ‖qVec Φ‖ := by
  have hu : Φ (uVec Φ) = e₀ n := by simp [uVec]
  have hw : Φ (wVec Φ) = Complex.I • e₀ n := by simp [wVec]
  have hee : (inner ℂ (e₀ n) (e₀ n) : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_e₀]; norm_num
  have hkey : (inner ℂ (uVec Φ) (wVec Φ) : ℂ).im = 1 := by
    have h := hΦ (uVec Φ) (wVec Φ)
    rw [hu, hw] at h
    rw [omegaForm, omegaForm, inner_smul_right, hee] at h
    simpa using h.symm
  have hcs : ‖(inner ℂ (uVec Φ) (wVec Φ) : ℂ)‖ ≤ ‖uVec Φ‖ * ‖wVec Φ‖ := norm_inner_le_norm _ _
  have h1 : (1:ℝ) ≤ ‖(inner ℂ (uVec Φ) (wVec Φ) : ℂ)‖ := by
    have h2 := Complex.abs_im_le_norm (inner ℂ (uVec Φ) (wVec Φ) : ℂ)
    rw [hkey] at h2
    simpa using h2
  have hp : ‖pVec Φ‖ = ‖wVec Φ‖ := by simp [pVec, norm_smul]
  have hq : ‖qVec Φ‖ = ‖uVec Φ‖ := by simp [qVec, norm_smul]
  rw [hp, hq, mul_comm]
  linarith

end

/-- **Linear Gromov nonsqueezing.**  If a linear symplectomorphism `Φ` of the standard
symplectic vector space `ℝ^{2(n+1)} = ℂ^{n+1}` maps the open ball of radius `r > 0` into the
open symplectic cylinder `Z(R) = {z : ‖z 0‖ < R}` of radius `R` over the first symplectic
coordinate plane, then `r ≤ R`.

This is the symplectic-linear case of Gromov's nonsqueezing theorem: a ball cannot be squeezed
by a symplectic map into a cylinder of smaller radius, however large the remaining directions
of the cylinder are (volume-preserving maps, by contrast, allow arbitrary squeezing). -/
