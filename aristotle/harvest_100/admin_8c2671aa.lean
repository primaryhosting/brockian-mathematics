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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-! ## Setup: the standard symplectic vector space -/

/-- The standard symplectic phase space `ℝ^{2n}`, with coordinates indexed by `ι ⊕ ι`:
`Sum.inl i` is the `i`-th position coordinate `qᵢ`, and `Sum.inr i` the `i`-th momentum
coordinate `pᵢ`.  It carries the standard Euclidean inner product. -/
abbrev Phase (ι : Type*) [Fintype ι] := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form `ω(x, y) = ∑ᵢ (qᵢ(x) pᵢ(y) - pᵢ(x) qᵢ(y))`. -/
noncomputable def omegaForm (x y : Phase ι) : ℝ :=
  ∑ i, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i))

/-- The standard complex structure `J`, satisfying `⟪J x, y⟫ = ω(x, y)`. -/
noncomputable def Jmap (x : Phase ι) : Phase ι :=
  WithLp.toLp 2 (fun k => Sum.elim (fun j => -x (Sum.inr j)) (fun j => x (Sum.inl j)) k)

/-- The open Euclidean ball of radius `r` in phase space. -/
def symplecticBall (r : ℝ) : Set (Phase ι) := {x | ‖x‖ < r}

/-- The open symplectic cylinder of radius `R` over the `i₀`-th coordinate plane,
i.e. the set of points whose `(q_{i₀}, p_{i₀})`-projection lies in the disc of radius `R`. -/
def symplecticCylinder (i₀ : ι) (R : ℝ) : Set (Phase ι) :=
  {y | y (Sum.inl i₀) ^ 2 + y (Sum.inr i₀) ^ 2 < R ^ 2}

/-! ## Basic properties of `J` and `ω` -/

@[simp] lemma Jmap_inl (x : Phase ι) (j : ι) : Jmap x (Sum.inl j) = -x (Sum.inr j) := by
  simp [Jmap]

@[simp] lemma Jmap_inr (x : Phase ι) (j : ι) : Jmap x (Sum.inr j) = x (Sum.inl j) := by
  simp [Jmap]

lemma inner_Jmap (x y : Phase ι) : ⟪Jmap x, y⟫ = omegaForm x y := by
  rw [PiLp.inner_apply, omegaForm, Fintype.sum_sum_type, Finset.sum_sub_distrib]
  simp [mul_comm]
  ring

lemma norm_Jmap (x : Phase ι) : ‖Jmap x‖ = ‖x‖ := by
  simp [EuclideanSpace.norm_eq, Fintype.sum_sum_type]
  ring_nf

lemma omegaForm_self (x : Phase ι) : omegaForm x x = 0 := by
  simp [omegaForm, mul_comm]

lemma omegaForm_zero_left (y : Phase ι) : omegaForm (0 : Phase ι) y = 0 := by
  simp [omegaForm]

lemma omegaForm_single_inr [DecidableEq ι] (i₀ : ι) (z : Phase ι) :
    omegaForm (EuclideanSpace.single (Sum.inr i₀) (1:ℝ)) z = -z (Sum.inl i₀) := by
  simp [omegaForm, EuclideanSpace.single_apply]

lemma omegaForm_single_inl [DecidableEq ι] (i₀ : ι) (z : Phase ι) :
    omegaForm (EuclideanSpace.single (Sum.inl i₀) (1:ℝ)) z = z (Sum.inr i₀) := by
  simp [omegaForm, EuclideanSpace.single_apply]

lemma omegaForm_single_single [DecidableEq ι] (i₀ : ι) :
    omegaForm (EuclideanSpace.single (Sum.inl i₀) (1:ℝ))
      (EuclideanSpace.single (Sum.inr i₀) (1:ℝ)) = 1 := by
  simp [omegaForm_single_inl, EuclideanSpace.single_apply]

/-! ## Elementary facts about orthogonal projections -/

section Proj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_proj_left (u v : E) (hu : u ≠ 0) : ⟪u, v - (⟪u, v⟫ / ‖u‖ ^ 2) • u⟫ = 0 := by
  have h : ‖u‖ ^ 2 ≠ 0 := by positivity
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  ring

lemma norm_proj_sq (u v : E) :
    ‖v - (⟪u, v⟫ / ‖u‖ ^ 2) • u‖ ^ 2
      = ‖v‖ ^ 2 - 2 * (⟪u, v⟫ / ‖u‖ ^ 2) * ⟪u, v⟫ + (⟪u, v⟫ / ‖u‖ ^ 2) ^ 2 * ‖u‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm v u, div_pow]
  ring

lemma inner_proj_right (u v : E) (hu : u ≠ 0) :
    ⟪v, v - (⟪u, v⟫ / ‖u‖ ^ 2) • u⟫ = ‖v - (⟪u, v⟫ / ‖u‖ ^ 2) • u‖ ^ 2 := by
  have h : ‖u‖ ^ 2 ≠ 0 := by positivity
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_proj_sq,
    real_inner_comm v u]
  field_simp
  ring

lemma norm_sq_mul_norm_proj_sq (u v : E) (hu : u ≠ 0) :
    ‖u‖ ^ 2 * ‖v - (⟪u, v⟫ / ‖u‖ ^ 2) • u‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  have h : ‖u‖ ^ 2 ≠ 0 := by positivity
  rw [norm_proj_sq]
  field_simp
  ring

end Proj

/-! ## The key linear-algebra estimate -/

/-- If two vectors `u`, `v` span a symplectic area equal to `1`, then their Gram determinant
is at least `1`. -/
lemma one_le_gram_of_omegaForm_eq_one {u v : Phase ι} (hu : u ≠ 0) (h : omegaForm u v = 1) :
    1 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  set c : ℝ := ⟪u, v⟫ / ‖u‖ ^ 2 with hc
  set w : Phase ι := v - c • u with hw
  have h1 : ⟪Jmap u, w⟫ = 1 := by
    rw [hw, inner_sub_right, real_inner_smul_right, inner_Jmap, inner_Jmap, omegaForm_self, h]
    ring
  have h2 : ⟪Jmap u, w⟫ ≤ ‖Jmap u‖ * ‖w‖ := real_inner_le_norm _ _
  have h3 : 1 ≤ ‖u‖ * ‖w‖ := by rw [norm_Jmap] at h2; linarith [h1 ▸ h2]
  have h4 : ‖u‖ ^ 2 * ‖w‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 :=
    norm_sq_mul_norm_proj_sq u v hu
  nlinarith [norm_nonneg u, norm_nonneg w]

/-- If `ω(u, v) = 1`, there is a unit vector `x` with `⟪u, x⟫² + ⟪v, x⟫² ≥ 1`. -/
lemma exists_unit_witness {u v : Phase ι} (h : omegaForm u v = 1) :
    ∃ x : Phase ι, ‖x‖ = 1 ∧ 1 ≤ ⟪u, x⟫ ^ 2 + ⟪v, x⟫ ^ 2 := by
  have hu : u ≠ 0 := by
    rintro rfl
    rw [omegaForm_zero_left] at h
    exact zero_ne_one h
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hgram : 1 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := one_le_gram_of_omegaForm_eq_one hu h
  by_cases hcase : 1 ≤ ‖u‖
  · refine ⟨‖u‖⁻¹ • u, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hun), inv_mul_cancel₀ hun.ne']
    · have : ⟪u, ‖u‖⁻¹ • u⟫ = ‖u‖ := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      rw [this]
      nlinarith [sq_nonneg (⟪v, ‖u‖⁻¹ • u⟫ : ℝ)]
  · push_neg at hcase
    set w : Phase ι := v - (⟪u, v⟫ / ‖u‖ ^ 2) • u with hw
    have h4 : ‖u‖ ^ 2 * ‖w‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 :=
      norm_sq_mul_norm_proj_sq u v hu
    have hw2 : 1 < ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    have hwn : 0 < ‖w‖ := by nlinarith [norm_nonneg w]
    refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwn), inv_mul_cancel₀ hwn.ne']
    · have hu' : ⟪u, ‖w‖⁻¹ • w⟫ = 0 := by
        rw [real_inner_smul_right, hw, inner_proj_left u v hu]
        ring
      have hv' : ⟪v, ‖w‖⁻¹ • w⟫ = ‖w‖ := by
        rw [real_inner_smul_right, hw, inner_proj_right u v hu, ← hw]
        field_simp
      rw [hu', hv']
      nlinarith

/-! ## Gromov's nonsqueezing theorem (linear case) -/

/-- **Gromov's nonsqueezing theorem**, linear case.

If a linear symplectomorphism `A` of the standard symplectic vector space `ℝ^{2n}`
maps the open ball of radius `r > 0` into the open symplectic cylinder of radius `R ≥ 0`
over the `i₀`-th coordinate plane, then `r ≤ R`.  In other words, a symplectic linear map
can never squeeze a ball into a thinner cylinder, no matter how large the dimension. -/
theorem gromov_nonsqueezing {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (r R : ℝ)
    (hr : 0 < r) (hR : 0 ≤ R) (A : Phase ι ≃ₗ[ℝ] Phase ι)
    (hA : ∀ x y : Phase ι, omegaForm (A x) (A y) = omegaForm x y)
    (hsub : A '' symplecticBall r ⊆ symplecticCylinder i₀ R) :
    r ≤ R := by
  -- the two coordinate vectors spanning the cylinder plane, and their `A`-preimages
  set e : Phase ι := EuclideanSpace.single (Sum.inl i₀) (1:ℝ) with he
  set f : Phase ι := EuclideanSpace.single (Sum.inr i₀) (1:ℝ) with hf
  set a : Phase ι := A.symm e with ha
  set b : Phase ι := A.symm f with hb
  set u : Phase ι := -(Jmap b) with hu
  set v : Phase ι := Jmap a with hv
  have hAa : A a = e := by rw [ha]; exact A.apply_symm_apply e
  have hAb : A b = f := by rw [hb]; exact A.apply_symm_apply f
  -- `u` and `v` represent the two coordinate functionals of the projection
  have hukey : ∀ x : Phase ι, ⟪u, x⟫ = (A x) (Sum.inl i₀) := by
    intro x
    have : ⟪u, x⟫ = -omegaForm b x := by rw [hu, inner_neg_left, inner_Jmap]
    rw [this, ← hA b x, hAb, hf, omegaForm_single_inr]
    ring
  have hvkey : ∀ x : Phase ι, ⟪v, x⟫ = (A x) (Sum.inr i₀) := by
    intro x
    have : ⟪v, x⟫ = omegaForm a x := by rw [hv, inner_Jmap]
    rw [this, ← hA a x, hAa, he, omegaForm_single_inl]
  -- the symplectic area spanned by `u` and `v` is `1`
  have homega : omegaForm u v = 1 := by
    have hJu : Jmap u = b := by
      rw [hu]
      ext k
      cases k <;> simp
    rw [← inner_Jmap, hJu, hv, real_inner_comm, inner_Jmap, ← hA a b, hAa, hAb, he, hf,
      omegaForm_single_single]
  obtain ⟨x, hx1, hx2⟩ := exists_unit_witness homega
  -- rescale `x` and use the containment
  have main : ∀ t : ℝ, 0 < t → t < r → t ^ 2 < R ^ 2 := by
    intro t ht htr
    have hmem : (t • x) ∈ symplecticBall (ι := ι) r := by
      have : ‖t • x‖ = t := by
        rw [norm_smul, hx1, Real.norm_eq_abs, abs_of_pos ht]; ring
      simpa [symplecticBall, this] using htr
    have := hsub ⟨t • x, hmem, rfl⟩
    rw [symplecticCylinder, Set.mem_setOf_eq, ← hukey, ← hvkey] at this
    have hus : ⟪u, t • x⟫ = t * ⟪u, x⟫ := real_inner_smul_right u x t
    have hvs : ⟪v, t • x⟫ = t * ⟪v, x⟫ := real_inner_smul_right v x t
    rw [hus, hvs] at this
    nlinarith [sq_nonneg t]
  by_contra hcon
  push_neg at hcon
  have h1 : 0 < (R + r) / 2 := by linarith
  have h2 : (R + r) / 2 < r := by linarith
  have := main _ h1 h2
  nlinarith

/-- The bound in `gromov_nonsqueezing` is sharp: the identity (a linear symplectomorphism)
maps the ball of radius `r` into the cylinder of radius `r`.  In particular the hypotheses of
`gromov_nonsqueezing` are satisfiable, so the theorem is not vacuous. -/
theorem id_ball_subset_cylinder [DecidableEq ι] (i₀ : ι) (r : ℝ) :
    (LinearEquiv.refl ℝ (Phase ι)) '' symplecticBall r ⊆ symplecticCylinder i₀ r := by
  rintro y ⟨x, hx, rfl⟩
  have hxr : ‖x‖ < r := hx
  have hnorm : ‖x‖ ^ 2 = ∑ k, (x k) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun k _ => sq_abs _
  have hpair : (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2
      = ∑ k ∈ ({Sum.inl i₀, Sum.inr i₀} : Finset (ι ⊕ ι)), (x k) ^ 2 := by
    rw [Finset.sum_pair (by simp)]
  have hle : ∑ k ∈ ({Sum.inl i₀, Sum.inr i₀} : Finset (ι ⊕ ι)), (x k) ^ 2 ≤ ∑ k, (x k) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => sq_nonneg _
  have : (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hpair, hnorm]; exact hle
  have hxnn : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
  show (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2 < r ^ 2
  nlinarith

end Math2

