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
noncomputable def omegaForm {n : ℕ} (z w : SympSpace n) : ℝ := (inner ℂ z w : ℂ).im

/-- A real-linear automorphism of `ℂ^{n+1}` is *symplectic* (a linear symplectomorphism)
if it preserves the standard symplectic form. -/
def IsSymplectic {n : ℕ} (Φ : SympSpace n ≃ₗ[ℝ] SympSpace n) : Prop :=
  ∀ z w : SympSpace n, omegaForm (Φ z) (Φ w) = omegaForm z w

/-- The identity is a linear symplectomorphism (so the hypotheses of the main theorem are
not vacuous). -/
lemma isSymplectic_refl (n : ℕ) : IsSymplectic (LinearEquiv.refl ℝ (SympSpace n)) :=
  fun _ _ => rfl

/-- The first standard basis vector, spanning (together with `i • e₀`) the first symplectic
coordinate plane. -/
noncomputable def e₀ (n : ℕ) : SympSpace n := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℂ)

lemma inner_e₀_left {n : ℕ} (z : SympSpace n) : (inner ℂ (e₀ n) z : ℂ) = z 0 := by
  simp [e₀, EuclideanSpace.inner_single_left]

lemma norm_e₀ (n : ℕ) : ‖e₀ n‖ = 1 := by
  simp [e₀, EuclideanSpace.norm_single]

section

variable {n : ℕ} (Φ : SympSpace n ≃ₗ[ℝ] SympSpace n)

/-- The preimage under `Φ` of the first basis vector. -/
noncomputable def uVec : SympSpace n := Φ.symm (e₀ n)

/-- The preimage under `Φ` of `i` times the first basis vector. -/
noncomputable def wVec : SympSpace n := Φ.symm (Complex.I • e₀ n)

/-- The vector representing the linear functional `v ↦ Re ((Φ v) 0)`. -/
noncomputable def pVec : SympSpace n := (-Complex.I) • wVec Φ

/-- The vector representing the linear functional `v ↦ Im ((Φ v) 0)`. -/
noncomputable def qVec : SympSpace n := Complex.I • uVec Φ

variable (hΦ : IsSymplectic Φ)

include hΦ

/-- Riesz-type representation of the imaginary part of the first coordinate of `Φ v`. -/
lemma im_coord_eq (v : SympSpace n) : ((Φ v) 0).im = (inner ℂ (qVec Φ) v : ℂ).re := by
  have hu : Φ (uVec Φ) = e₀ n := by simp [uVec]
  have h1 : (inner ℂ (uVec Φ) v : ℂ).im = ((Φ v) 0).im := by
    have h := hΦ (uVec Φ) v
    rw [hu] at h
    rw [omegaForm, omegaForm, inner_e₀_left] at h
    exact h.symm
  rw [qVec, inner_smul_left]
  simp [← h1]

/-- Riesz-type representation of the real part of the first coordinate of `Φ v`. -/
lemma re_coord_eq (v : SympSpace n) : ((Φ v) 0).re = (inner ℂ (pVec Φ) v : ℂ).re := by
  have hw : Φ (wVec Φ) = Complex.I • e₀ n := by simp [wVec]
  have h1 : (inner ℂ (wVec Φ) v : ℂ).im = -((Φ v) 0).re := by
    have h := hΦ (wVec Φ) v
    rw [hw] at h
    rw [omegaForm, omegaForm, inner_smul_left, inner_e₀_left] at h
    simp at h
    linarith [h]
  rw [pVec, inner_smul_left]
  simp [h1]

/-- The two representing vectors are large enough: `‖p‖ * ‖q‖ ≥ 1`.  This is where the
symplectic condition enters: `p` and `q` are (up to multiplication by `i`) a pair of vectors
with `ω = 1`, hence by Cauchy-Schwarz their norms multiply to at least `1`. -/
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
theorem gromov_nonsqueezing {n : ℕ} {r R : ℝ} (hr : 0 < r)
    (Φ : SympSpace n ≃ₗ[ℝ] SympSpace n) (hΦ : IsSymplectic Φ)
    (hsq : ∀ z : SympSpace n, ‖z‖ < r → ‖(Φ z) 0‖ < R) : r ≤ R := by
  -- From a representing vector of norm at least `1` we get `t < R` for every `0 ≤ t < r`.
  have main : ∀ p : SympSpace n, 1 ≤ ‖p‖ →
      (∀ v : SympSpace n, |(inner ℂ p v : ℂ).re| ≤ ‖(Φ v) 0‖) → r ≤ R := by
    intro p hp hrep
    have hp0 : (0:ℝ) < ‖p‖ := lt_of_lt_of_le zero_lt_one hp
    have key : ∀ t : ℝ, 0 ≤ t → t < r → t < R := by
      intro t ht htr
      set c : ℝ := t / ‖p‖ with hc
      have hc0 : 0 ≤ c := div_nonneg ht hp0.le
      set v : SympSpace n := ((c : ℂ)) • p with hv
      have hnv : ‖v‖ = t := by
        rw [hv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0, hc,
          div_mul_cancel₀ _ (ne_of_gt hp0)]
      have hself : (inner ℂ p p : ℂ).re = ‖p‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]; norm_cast
      have hselfim : (inner ℂ p p : ℂ).im = 0 := by simpa using inner_self_im (𝕜 := ℂ) p
      have hinner : (inner ℂ p v : ℂ).re = t * ‖p‖ := by
        rw [hv, inner_smul_right, Complex.mul_re, hself, hselfim, Complex.ofReal_re, hc]
        field_simp
        ring
      have h1 : t ≤ |(inner ℂ p v : ℂ).re| := by
        rw [hinner, abs_of_nonneg (by positivity)]
        nlinarith
      exact lt_of_le_of_lt (le_trans h1 (hrep v)) (hsq v (by rw [hnv]; exact htr))
    by_contra hcon
    push_neg at hcon
    rcases le_or_gt 0 R with hR | hR
    · exact absurd (key R hR hcon) (lt_irrefl R)
    · exact absurd (key 0 le_rfl hr) (not_lt.mpr hR.le)
  have hprod := one_le_norm_pVec_mul_norm_qVec Φ hΦ
  rcases le_or_gt 1 ‖pVec Φ‖ with h | h
  · refine main (pVec Φ) h (fun v => ?_)
    rw [← re_coord_eq Φ hΦ v]
    exact Complex.abs_re_le_norm _
  · have hq : 1 ≤ ‖qVec Φ‖ := by
      nlinarith [norm_nonneg (pVec Φ), norm_nonneg (qVec Φ)]
    refine main (qVec Φ) hq (fun v => ?_)
    rw [← im_coord_eq Φ hΦ v]
    exact Complex.abs_im_le_norm _

/-- **Linear Gromov nonsqueezing, for symplectic linear maps.**  The invertibility assumption
in `Math2.gromov_nonsqueezing` is automatic: any real-linear map preserving the standard
symplectic form is injective, hence bijective in finite dimension.  So if a real-linear map
`Φ` preserving `ω` sends the open ball of radius `r > 0` into the open cylinder
`Z(R) = {z : ‖z 0‖ < R}`, then `r ≤ R`. -/
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

