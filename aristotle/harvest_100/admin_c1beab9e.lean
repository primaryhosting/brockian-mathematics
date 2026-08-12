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
def omegaForm {n : ℕ} (z w : SymplecticSpace n) : ℝ := (⟪z, w⟫_ℂ).im

/-- A real-linear map of `ℂ^n ≃ ℝ^{2n}` is symplectic when it preserves the standard
symplectic form. -/
def IsLinearSymplectic {n : ℕ} (Φ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n) : Prop :=
  ∀ z w, omegaForm (Φ z) (Φ w) = omegaForm z w

/-- The open ball of radius `r` centred at the origin. -/
def openBall {n : ℕ} (r : ℝ) : Set (SymplecticSpace n) := {z | ‖z‖ < r}

/-- The open symplectic cylinder `Z(R) = B²(R) × ℂ^{n-1}` of radius `R`: the set of points
whose first complex coordinate has modulus `< R`. -/
def openCylinder {n : ℕ} [NeZero n] (R : ℝ) : Set (SymplecticSpace n) := {z | ‖z 0‖ < R}

/-! ### Basic properties of the symplectic form -/

/-- The symplectic form is the real inner product against multiplication by `I`. -/
lemma omegaForm_eq_real_inner {n : ℕ} (z w : SymplecticSpace n) :
    omegaForm z w = ⟪(Complex.I • z), w⟫_ℝ := by
  rw [omegaForm, PiLp.inner_apply, PiLp.inner_apply]
  simp [Complex.im_sum]
  rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Multiplication by `I` is an isometry for the real inner product. -/
lemma real_inner_I_smul_I_smul {n : ℕ} (z w : SymplecticSpace n) :
    ⟪(Complex.I • z), (Complex.I • w)⟫_ℝ = ⟪z, w⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

lemma I_smul_I_smul {n : ℕ} (z : SymplecticSpace n) :
    Complex.I • (Complex.I • z) = -z := by
  rw [smul_smul]; simp

lemma norm_I_smul {n : ℕ} (z : SymplecticSpace n) : ‖Complex.I • z‖ = ‖z‖ := by
  rw [norm_smul]; simp

/-- Skew-adjointness of multiplication by `I` for the real inner product. -/
lemma real_inner_I_smul_left {n : ℕ} (z w : SymplecticSpace n) :
    ⟪(Complex.I • z), w⟫_ℝ = -⟪z, (Complex.I • w)⟫_ℝ := by
  conv_lhs => rw [← real_inner_I_smul_I_smul (Complex.I • z) w, I_smul_I_smul]
  rw [inner_neg_left]

/-- The symplectic form is bounded by the Euclidean norms. -/
lemma abs_omegaForm_le {n : ℕ} (z w : SymplecticSpace n) :
    |omegaForm z w| ≤ ‖z‖ * ‖w‖ := by
  rw [omegaForm_eq_real_inner]
  calc |⟪(Complex.I • z), w⟫_ℝ| ≤ ‖Complex.I • z‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ = ‖z‖ * ‖w‖ := by rw [norm_I_smul]

/-! ### The adjoint of a linear symplectic map is symplectic -/

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

lemma symplectic_injective {n : ℕ} {Φ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n}
    (hΦ : IsLinearSymplectic Φ) : Function.Injective Φ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h0 := adjoint_I_smul_apply hΦ u
  rw [hu] at h0
  simp at h0
  have h1 : Complex.I • u = 0 := h0.symm
  have h2 : Complex.I • (Complex.I • u) = 0 := by rw [h1]; simp
  rw [I_smul_I_smul] at h2
  simpa using h2

lemma symplectic_surjective {n : ℕ} {Φ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n}
    (hΦ : IsLinearSymplectic Φ) : Function.Surjective Φ :=
  LinearMap.surjective_of_injective (symplectic_injective hΦ)

/-- If `Φ` is linear symplectic, so is its adjoint. -/
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

lemma real_inner_single_one_left {n : ℕ} [NeZero n] (w : SymplecticSpace n) :
    ⟪(EuclideanSpace.single (0 : Fin n) (1 : ℂ) : SymplecticSpace n), w⟫_ℝ = (w 0).re := by
  rw [PiLp.inner_apply]
  simp [EuclideanSpace.single_apply, apply_ite Complex.re, Finset.sum_ite_eq']

lemma real_inner_I_single_one_left {n : ℕ} [NeZero n] (w : SymplecticSpace n) :
    ⟪(Complex.I • (EuclideanSpace.single (0 : Fin n) (1 : ℂ) : SymplecticSpace n)), w⟫_ℝ
      = (w 0).im := by
  rw [PiLp.inner_apply]
  simp [EuclideanSpace.single_apply, apply_ite Complex.re, apply_ite Complex.im, mul_ite,
    Finset.sum_ite_eq']

/-! ### The main estimate -/

/-- If the linear functional `⟪c, ·⟫` is bounded by `R` on the ball of radius `r`,
then `r * ‖c‖ ≤ R`. -/
lemma norm_le_of_inner_bound {n : ℕ} {c : SymplecticSpace n} {r R : ℝ}
    (hR : 0 ≤ R) (h : ∀ v : SymplecticSpace n, ‖v‖ < r → ⟪c, v⟫_ℝ < R) :
    r * ‖c‖ ≤ R := by
  by_contra hcon
  push_neg at hcon
  have hc : 0 < ‖c‖ := by
    rcases (norm_nonneg c).lt_or_eq with h1 | h1
    · exact h1
    · exfalso; rw [← h1] at hcon; simp at hcon; linarith
  set t : ℝ := (R / ‖c‖ + r) / 2 with ht
  have h1 : R / ‖c‖ < r := by rw [div_lt_iff₀ hc]; linarith
  have h2 : R / ‖c‖ < t := by rw [ht]; linarith
  have h3 : t < r := by rw [ht]; linarith
  have h4 : 0 < t := lt_of_le_of_lt (div_nonneg hR hc.le) h2
  have hv : ‖(t / ‖c‖) • c‖ = t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos h4 hc)]
    field_simp
  have hlt := h ((t / ‖c‖) • c) (by rw [hv]; exact h3)
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at hlt
  have h5 : t * ‖c‖ < R := by
    calc t * ‖c‖ = t / ‖c‖ * ‖c‖ ^ 2 := by field_simp
      _ < R := hlt
  rw [div_lt_iff₀ hc] at h2
  linarith

/-- The analytic core of the nonsqueezing statement: if a linear symplectic map sends every
vector of norm `< r` to a vector whose first complex coordinate has modulus `< R`, then
`r ≤ R`. -/
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
theorem gromov_nonsqueezing {n : ℕ} [NeZero n] {r R : ℝ} (hr : 0 < r)
    (Φ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n) (hΦ : IsLinearSymplectic Φ)
    (hsub : Φ '' (openBall r) ⊆ openCylinder R) : r ≤ R :=
  nonsqueezing_core hr Φ hΦ (fun v hv => hsub ⟨v, hv, rfl⟩)

/-- **Gromov's nonsqueezing theorem, affine case.**
The same conclusion for an arbitrary affine symplectic map `v ↦ Φ v + w`, an arbitrary ball
`{v | ‖v - c‖ < r}` and an arbitrary cylinder `{z | ‖z 0 - p‖ < R}` whose axis is any
translate of the complex hyperplane. -/
theorem gromov_nonsqueezing_affine {n : ℕ} [NeZero n] {r R : ℝ} (hr : 0 < r)
    (Φ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n) (hΦ : IsLinearSymplectic Φ)
    (c w : SymplecticSpace n) (p : ℂ)
    (hsub : ∀ v : SymplecticSpace n, ‖v - c‖ < r → ‖(Φ v + w) 0 - p‖ < R) : r ≤ R := by
  refine nonsqueezing_core hr Φ hΦ ?_
  intro u hu
  have h1 := hsub (c + u) (by simpa using hu)
  have h2 := hsub (c - u) (by simpa using hu)
  have e1 : (Φ (c + u) + w) 0 - p = ((Φ c + w) 0 - p) + (Φ u) 0 := by
    simp [map_add]; ring
  have e2 : (Φ (c - u) + w) 0 - p = ((Φ c + w) 0 - p) - (Φ u) 0 := by
    simp [map_sub]; ring
  rw [e1] at h1
  rw [e2] at h2
  have key : ∀ A X : ℂ, ‖X‖ ≤ (‖A + X‖ + ‖A - X‖) / 2 := by
    intro A X
    have h := norm_sub_le (A + X) (A - X)
    have h3 : (A + X) - (A - X) = (2 : ℂ) * X := by ring
    rw [h3, norm_mul] at h
    have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h4] at h
    linarith
  have h5 := key ((Φ c + w) 0 - p) ((Φ u) 0)
  linarith

/-! ### Sharpness

The hypotheses of `gromov_nonsqueezing` are satisfiable and the bound `r ≤ R` is optimal:
the identity is a linear symplectic map taking the ball of radius `r` into the cylinder of
radius `r`. -/

lemma isLinearSymplectic_id {n : ℕ} :
    IsLinearSymplectic (LinearMap.id : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n) :=
  fun _ _ => rfl

lemma id_image_openBall_subset_openCylinder {n : ℕ} [NeZero n] (r : ℝ) :
    (LinearMap.id : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n) '' (openBall r)
      ⊆ openCylinder r := by
  rintro z ⟨v, hv, rfl⟩
  exact lt_of_le_of_lt (PiLp.norm_apply_le v 0) hv

end

end Math2

