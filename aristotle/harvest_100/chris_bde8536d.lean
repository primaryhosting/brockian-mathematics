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
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

/-! ## The standard symplectic vector space `ℝ^{2n}`

We model `ℝ^{2n}` as the Euclidean space indexed by `Fin n × Fin 2`, where for each
`i : Fin n` the coordinate `(i,0)` is the position `x i` and `(i,1)` is the momentum `y i`.
-/

/-- The standard `2n`-dimensional Euclidean/symplectic vector space. -/
abbrev V (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard symplectic form `ω(u,v) = ∑ i, (u_{x i} v_{y i} - u_{y i} v_{x i})`. -/
noncomputable def omg {n : ℕ} (u v : V n) : ℝ :=
  ∑ i : Fin n, (u.ofLp (i, 0) * v.ofLp (i, 1) - u.ofLp (i, 1) * v.ofLp (i, 0))

/-- The standard complex structure `J`, sending `(x, y) ↦ (-y, x)`. -/
noncomputable def Jm {n : ℕ} (z : V n) : V n :=
  WithLp.toLp 2 (fun p => if p.2 = 0 then -(z.ofLp (p.1, 1)) else z.ofLp (p.1, 0))

/-- The open ball of radius `r` centered at the origin. -/
def ball (n : ℕ) (r : ℝ) : Set (V n) := {z | ‖z‖ < r}

/-- The open symplectic cylinder of radius `R`: the set of points whose first
position/momentum pair `(x₀, y₀)` lies in the open disc of radius `R`. -/
def cyl (n : ℕ) (R : ℝ) : Set (V (n + 1)) :=
  {z | (z.ofLp ((0 : Fin (n + 1)), (0 : Fin 2))) ^ 2
        + (z.ofLp ((0 : Fin (n + 1)), (1 : Fin 2))) ^ 2 < R ^ 2}

/-! ## Basic properties of `J` and `ω` -/

@[simp] lemma Jm_apply_zero {n : ℕ} (z : V n) (i : Fin n) :
    (Jm z).ofLp (i, 0) = -(z.ofLp (i, 1)) := by
  simp [Jm]

@[simp] lemma Jm_apply_one {n : ℕ} (z : V n) (i : Fin n) :
    (Jm z).ofLp (i, 1) = z.ofLp (i, 0) := by
  simp [Jm]

lemma inner_eq_sum {n : ℕ} (u v : V n) : ⟪u, v⟫ = ∑ p, u.ofLp p * v.ofLp p := by
  simp [PiLp.inner_apply, mul_comm]

lemma sum_prod_fin2 {n : ℕ} (f : Fin n × Fin 2 → ℝ) :
    ∑ p, f p = ∑ i : Fin n, (f (i, 0) + f (i, 1)) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun i _ => by simp [Fin.sum_univ_two])

lemma omg_eq_inner {n : ℕ} (u v : V n) : omg u v = ⟪Jm u, v⟫ := by
  rw [inner_eq_sum, sum_prod_fin2, omg]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp
  ring

lemma Jm_neg {n : ℕ} (z : V n) : Jm (-z) = -(Jm z) := by
  ext p
  obtain ⟨i, j⟩ := p
  fin_cases j <;> simp [Jm]

lemma Jm_Jm {n : ℕ} (z : V n) : Jm (Jm z) = -z := by
  ext p
  obtain ⟨i, j⟩ := p
  fin_cases j <;> simp [Jm]

lemma inner_Jm_Jm {n : ℕ} (u v : V n) : ⟪Jm u, Jm v⟫ = ⟪u, v⟫ := by
  rw [inner_eq_sum, inner_eq_sum, sum_prod_fin2, sum_prod_fin2]
  exact Finset.sum_congr rfl (fun i _ => by simp; ring)

lemma norm_Jm {n : ℕ} (z : V n) : ‖Jm z‖ = ‖z‖ := by
  rw [← Real.sqrt_mul_self (norm_nonneg (Jm z)), ← Real.sqrt_mul_self (norm_nonneg z),
    ← real_inner_self_eq_norm_mul_norm, ← real_inner_self_eq_norm_mul_norm, inner_Jm_Jm]

lemma inner_Jm_self {n : ℕ} (z : V n) : ⟪z, Jm z⟫ = 0 := by
  rw [inner_eq_sum, sum_prod_fin2]
  exact Finset.sum_eq_zero (fun i _ => by simp; ring)

lemma omg_neg_neg {n : ℕ} (u v : V n) : omg (-u) (-v) = omg u v := by
  simp [omg]

lemma omg_Jm_Jm {n : ℕ} (u v : V n) : omg (Jm u) (Jm v) = omg u v := by
  unfold omg
  exact Finset.sum_congr rfl (fun i _ => by simp; ring)

/-! ## Two lemmas of Euclidean geometry -/

/-- Gram-type bound: if `c ⟂ a` and `‖c‖ = ‖a‖` then `⟪c,b⟫² ≤ ‖a‖²‖b‖² - ⟪a,b⟫²`. -/
lemma gram_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a c b : E) (h1 : ⟪a, c⟫ = 0) (h2 : ‖c‖ = ‖a‖) :
    ⟪c, b⟫ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hc : c = 0 := by rw [← norm_eq_zero, h2]; simp
    simp [hc]
  have hA : (0:ℝ) < ‖a‖ ^ 2 := by positivity
  set A : ℝ := ‖a‖ ^ 2 with hAdef
  set p : E := b - (⟪a, b⟫ / A) • a - (⟪c, b⟫ / A) • c with hp
  have h0 : (0:ℝ) ≤ ⟪p, p⟫ := real_inner_self_nonneg
  have hcc : ⟪c, c⟫ = A := by rw [real_inner_self_eq_norm_sq, h2]
  have haa : ⟪a, a⟫ = A := real_inner_self_eq_norm_sq a
  have hbb : ⟪b, b⟫ = ‖b‖ ^ 2 := real_inner_self_eq_norm_sq b
  have hca : ⟪c, a⟫ = 0 := by rw [real_inner_comm]; exact h1
  have hexp : ⟪p, p⟫ = ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 / A - ⟪c, b⟫ ^ 2 / A := by
    simp only [hp, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      h1, hca, hcc, haa, hbb, real_inner_comm b a, real_inner_comm b c]
    field_simp
    ring
  rw [hexp] at h0
  have h0' : ⟪a, b⟫ ^ 2 / A * A + ⟪c, b⟫ ^ 2 / A * A ≤ ‖b‖ ^ 2 * A :=
    by nlinarith [mul_nonneg h0 hA.le]
  rw [div_mul_cancel₀ _ hA.ne', div_mul_cancel₀ _ hA.ne'] at h0'
  linarith

/-- **Key intermediate lemma.**  If the Gram determinant of `a, b` is at least `1`,
then some unit vector `w` satisfies `⟪a,w⟫² + ⟪b,w⟫² ≥ 1`; i.e. the image of the unit
ball under `z ↦ (⟪a,z⟫, ⟪b,z⟫)` is not contained in any disc of radius `< 1`. -/
lemma exists_unit_of_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (h : 1 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2) :
    ∃ w : E, ‖w‖ = 1 ∧ 1 ≤ ⟪a, w⟫ ^ 2 + ⟪b, w⟫ ^ 2 := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h
    linarith [h]
  have hA : (0:ℝ) < ‖a‖ ^ 2 := by positivity
  rcases le_or_gt 1 (‖a‖ ^ 2) with hcase | hcase
  · refine ⟨‖a‖⁻¹ • a, ?_, ?_⟩
    · rw [norm_smul]
      simp [norm_ne_zero_iff.mpr ha]
    · have hval : ⟪a, ‖a‖⁻¹ • a⟫ = ‖a‖ := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      rw [hval]
      nlinarith [sq_nonneg ⟪b, ‖a‖⁻¹ • a⟫]
  · set q : E := b - (⟪a, b⟫ / ‖a‖ ^ 2) • a with hq
    have haa : ⟪a, a⟫ = ‖a‖ ^ 2 := real_inner_self_eq_norm_sq a
    have hbb : ⟪b, b⟫ = ‖b‖ ^ 2 := real_inner_self_eq_norm_sq b
    have haq : ⟪a, q⟫ = 0 := by
      simp only [hq, inner_sub_right, real_inner_smul_right, haa]
      field_simp
      ring
    have hqq : ⟪q, q⟫ = (‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2) / ‖a‖ ^ 2 := by
      simp only [hq, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        haa, hbb, real_inner_comm b a]
      field_simp
      ring
    have hbq : ⟪b, q⟫ = ⟪q, q⟫ := by
      have hexp : ⟪q, q⟫ = ⟪b, q⟫ - (⟪a, b⟫ / ‖a‖ ^ 2) * ⟪a, q⟫ := by
        rw [hq]
        simp only [inner_sub_left, real_inner_smul_left]
      rw [hexp, haq]
      ring
    have hqn : ‖q‖ ^ 2 = ⟪q, q⟫ := (real_inner_self_eq_norm_sq q).symm
    have hqpos : 1 < ‖q‖ ^ 2 := by
      rw [hqn, hqq, lt_div_iff₀ hA]
      nlinarith
    have hq0 : q ≠ 0 := by
      intro h0
      rw [h0] at hqpos
      simp at hqpos
      linarith
    refine ⟨‖q‖⁻¹ • q, ?_, ?_⟩
    · rw [norm_smul]
      simp [norm_ne_zero_iff.mpr hq0]
    · have hval : ⟪b, ‖q‖⁻¹ • q⟫ = ‖q‖ := by
        rw [real_inner_smul_right, hbq, ← hqn]
        field_simp
      rw [hval]
      nlinarith [sq_nonneg ⟪a, ‖q‖⁻¹ • q⟫]

/-! ## Gromov nonsqueezing (linear case) -/

/-- Gromov's nonsqueezing theorem for linear symplectomorphisms: a linear
symplectomorphism of the standard symplectic vector space `ℝ^{2(n+1)}` cannot map the
open ball of radius `r` into the open symplectic cylinder of radius `R` unless `r ≤ R`. -/
theorem gromov_nonsqueezing {n : ℕ} {r R : ℝ} (hR : 0 ≤ R)
    (Φ : V (n + 1) ≃ₗ[ℝ] V (n + 1)) (hΦ : ∀ u v, omg (Φ u) (Φ v) = omg u v)
    (hsub : Φ '' ball (n + 1) r ⊆ cyl n R) : r ≤ R := by
  by_contra hcon
  push_neg at hcon
  -- the inverse map is symplectic too
  have hΦs : ∀ u v, omg (Φ.symm u) (Φ.symm v) = omg u v := by
    intro u v
    have := hΦ (Φ.symm u) (Φ.symm v)
    simpa using this.symm
  set e : V (n + 1) := EuclideanSpace.single ((0 : Fin (n + 1)), (0 : Fin 2)) (1:ℝ) with he
  set f : V (n + 1) := EuclideanSpace.single ((0 : Fin (n + 1)), (1 : Fin 2)) (1:ℝ) with hf
  set a : V (n + 1) := Jm (Φ.symm (-(Jm e))) with ha
  set b : V (n + 1) := Jm (Φ.symm (-(Jm f))) with hb
  -- the coordinate functionals of `Φ` are represented by `a` and `b`
  have repr : ∀ (w z : V (n + 1)), ⟪w, Φ z⟫ = ⟪Jm (Φ.symm (-(Jm w))), z⟫ := by
    intro w z
    have h1 : ⟪w, Φ z⟫ = omg (-(Jm w)) (Φ z) := by
      rw [omg_eq_inner, Jm_neg, Jm_Jm]
      simp
    have h2 : omg (-(Jm w)) (Φ z) = omg (Φ (Φ.symm (-(Jm w)))) (Φ z) := by simp
    rw [h1, h2, hΦ, omg_eq_inner]
  -- `ω(a,b) = 1`
  have homg_ef : omg e f = 1 := by
    simp [omg, he, hf, EuclideanSpace.single_apply]
  have homgab : omg a b = 1 := by
    rw [ha, hb, omg_Jm_Jm, hΦs, omg_neg_neg, omg_Jm_Jm, homg_ef]
  have hgram : 1 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a, b⟫ ^ 2 := by
    have hg := gram_bound a (Jm a) b (inner_Jm_self a) (norm_Jm a)
    rw [← omg_eq_inner, homgab] at hg
    linarith
  obtain ⟨w, hw1, hw2⟩ := exists_unit_of_gram a b hgram
  -- the point `R • w` lies in the ball, hence its image lies in the cylinder
  have hmem : Φ (R • w) ∈ cyl n R := by
    refine hsub ⟨R • w, ?_, rfl⟩
    simp only [ball, Set.mem_setOf_eq, norm_smul, hw1, mul_one, Real.norm_eq_abs,
      abs_of_nonneg hR]
    exact hcon
  have hc0 : (Φ (R • w)).ofLp ((0 : Fin (n + 1)), (0 : Fin 2)) = R * ⟪a, w⟫ := by
    have := repr e (R • w)
    rw [he] at this
    rw [EuclideanSpace.inner_single_left] at this
    simp only [map_one, one_mul] at this
    rw [this, ← ha, real_inner_smul_right]
  have hc1 : (Φ (R • w)).ofLp ((0 : Fin (n + 1)), (1 : Fin 2)) = R * ⟪b, w⟫ := by
    have := repr f (R • w)
    rw [hf] at this
    rw [EuclideanSpace.inner_single_left] at this
    simp only [map_one, one_mul] at this
    rw [this, ← hb, real_inner_smul_right]
  simp only [cyl, Set.mem_setOf_eq, hc0, hc1, mul_pow] at hmem
  nlinarith [sq_nonneg R, hmem, hw2]

/-- Sharpness (and non-vacuity) of the previous theorem: whenever `r ≤ R`, the identity
linear symplectomorphism does map the ball of radius `r` into the cylinder of radius `R`. -/
theorem ball_subset_cyl {n : ℕ} {r R : ℝ} (h : r ≤ R) :
    (LinearEquiv.refl ℝ (V (n + 1))) '' ball (n + 1) r ⊆ cyl n R := by
  rintro _ ⟨z, hz, rfl⟩
  simp only [ball, Set.mem_setOf_eq] at hz
  have hnorm : ‖z‖ ^ 2 = ∑ p, (z.ofLp p) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_sum]
    exact Finset.sum_congr rfl (fun p _ => (sq (z.ofLp p)).symm)
  have hpair : ((0 : Fin (n + 1)), (0 : Fin 2)) ≠ ((0 : Fin (n + 1)), (1 : Fin 2)) := by
    simp
  have hle : (z.ofLp ((0 : Fin (n + 1)), (0 : Fin 2))) ^ 2
      + (z.ofLp ((0 : Fin (n + 1)), (1 : Fin 2))) ^ 2 ≤ ∑ p, (z.ofLp p) ^ 2 := by
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun p : Fin (n + 1) × Fin 2 => (z.ofLp p) ^ 2)
      (Finset.subset_univ ({((0 : Fin (n + 1)), (0 : Fin 2)),
        ((0 : Fin (n + 1)), (1 : Fin 2))} : Finset (Fin (n + 1) × Fin 2)))
      (fun p _ _ => sq_nonneg _)
    rwa [Finset.sum_pair hpair] at hsum
  simp only [LinearEquiv.refl_apply, cyl, Set.mem_setOf_eq]
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hz2 : ‖z‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg z]
  nlinarith [hle, hnorm, hz2]

end Math2

