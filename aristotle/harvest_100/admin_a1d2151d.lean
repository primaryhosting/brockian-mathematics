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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-- The symplectic vector space `ℝ^{2n}`, modelled as the Euclidean space indexed by `ι ⊕ ι`:
the `Sum.inl` coordinates are the "positions" and the `Sum.inr` coordinates the "momenta". -/
abbrev SymplecticSpace (ι : Type*) [Fintype ι] : Type _ := EuclideanSpace ℝ (ι ⊕ ι)

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form on `ℝ^{2n} = ℝ^ι × ℝ^ι`,
`ω(u, v) = ∑ i, (u_i v_{n+i} - u_{n+i} v_i)`. -/
noncomputable def symplecticForm (u v : SymplecticSpace ι) : ℝ :=
  ∑ i : ι, (u (Sum.inl i) * v (Sum.inr i) - u (Sum.inr i) * v (Sum.inl i))

/-- The standard complex structure `J` on `ℝ^{2n}`, chosen so that
`ω (u, v) = ⟪u, J v⟫`. -/
noncomputable def cxStructure (v : SymplecticSpace ι) : SymplecticSpace ι :=
  (WithLp.equiv 2 _).symm (fun j => Sum.rec (fun i => v (Sum.inr i)) (fun i => -v (Sum.inl i)) j)

/-- The symplectic cylinder of radius `R` in the direction of the coordinate plane `i₀`. -/
def cylinder [DecidableEq ι] (i₀ : ι) (R : ℝ) : Set (SymplecticSpace ι) :=
  {v | (v (Sum.inl i₀)) ^ 2 + (v (Sum.inr i₀)) ^ 2 < R ^ 2}

@[simp]
theorem cxStructure_inl (v : SymplecticSpace ι) (i : ι) :
    (cxStructure v) (Sum.inl i) = v (Sum.inr i) := by
  simp [cxStructure]

@[simp]
theorem cxStructure_inr (v : SymplecticSpace ι) (i : ι) :
    (cxStructure v) (Sum.inr i) = -v (Sum.inl i) := by
  simp [cxStructure]

theorem norm_cxStructure (v : SymplecticSpace ι) : ‖cxStructure v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [cxStructure_inl, cxStructure_inr, norm_neg]
  ring

/-- The symplectic form is the inner product against the complex structure. -/
theorem symplecticForm_eq_inner (u v : SymplecticSpace ι) :
    symplecticForm u v = ⟪u, cxStructure v⟫ := by
  rw [PiLp.inner_apply, Fintype.sum_sum_type, symplecticForm]
  simp only [RCLike.inner_apply, conj_trivial, cxStructure_inl, cxStructure_inr]
  rw [Finset.sum_sub_distrib]
  simp [mul_comm, sub_eq_add_neg]

theorem symplecticForm_antisymm (u v : SymplecticSpace ι) :
    symplecticForm u v = -symplecticForm v u := by
  simp only [symplecticForm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Cauchy–Schwarz for the symplectic form. -/
theorem abs_symplecticForm_le (u v : SymplecticSpace ι) :
    |symplecticForm u v| ≤ ‖u‖ * ‖v‖ := by
  rw [symplecticForm_eq_inner]
  calc |⟪u, cxStructure v⟫| ≤ ‖u‖ * ‖cxStructure v‖ := abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ := by rw [norm_cxStructure]

/-- If the linear functional `x ↦ ω(x, w)` is bounded by `R` in absolute value on the
ball of radius `r`, then `r * ‖w‖ ≤ R`: the bound is attained in the limit. -/
theorem radius_mul_norm_le (r R : ℝ) (hR : 0 ≤ R) (w : SymplecticSpace ι)
    (h : ∀ x : SymplecticSpace ι, ‖x‖ < r → (symplecticForm x w) ^ 2 < R ^ 2) :
    r * ‖w‖ ≤ R := by
  by_contra hcon
  push_neg at hcon
  have hw : 0 < ‖w‖ := by
    rcases (norm_nonneg w).lt_or_eq with h' | h'
    · exact h'
    · exfalso; rw [← h'] at hcon; simp at hcon; linarith
  set t : ℝ := R / ‖w‖ with ht
  have ht0 : 0 ≤ t := div_nonneg hR hw.le
  have htr : t < r := by
    rw [ht, div_lt_iff₀ hw]
    linarith [hcon]
  set x : SymplecticSpace ι := (t / ‖w‖) • cxStructure w with hx
  have hxnorm : ‖x‖ = t := by
    rw [hx, norm_smul, norm_cxStructure]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg ht0 hw.le)]
    field_simp
  have hval : symplecticForm x w = R := by
    rw [symplecticForm_eq_inner, hx, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_cxStructure]
    rw [ht]
    field_simp
  have := h x (by rw [hxnorm]; exact htr)
  rw [hval] at this
  linarith

@[simp]
theorem symplecticForm_single_right [DecidableEq ι] (u : SymplecticSpace ι) (i : ι) :
    symplecticForm u (EuclideanSpace.single (Sum.inr i) (1 : ℝ)) = u (Sum.inl i) := by
  simp [symplecticForm, EuclideanSpace.single_apply]

@[simp]
theorem symplecticForm_single_left [DecidableEq ι] (u : SymplecticSpace ι) (i : ι) :
    symplecticForm (EuclideanSpace.single (Sum.inl i) (1 : ℝ)) u = u (Sum.inr i) := by
  simp [symplecticForm, EuclideanSpace.single_apply]

/-- **Linear Gromov nonsqueezing.**

If a linear symplectomorphism `Φ` of the standard symplectic vector space `ℝ^{2n}` maps the
open ball of radius `r` around the origin into the open symplectic cylinder
`Z(R) = {v | v_{i₀}² + v_{n+i₀}² < R²}`, then `r ≤ R`.

(This is the linear case of Gromov's nonsqueezing theorem: no symplectic linear map can squeeze
a ball into a thinner symplectic cylinder, even though maps of arbitrarily large distortion
preserving volume exist.) -/
theorem gromov_nonsqueezing {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (r R : ℝ)
    (hr : 0 < r) (hR : 0 ≤ R)
    (Φ : SymplecticSpace ι ≃ₗ[ℝ] SymplecticSpace ι)
    (hsymp : ∀ u v : SymplecticSpace ι, symplecticForm (Φ u) (Φ v) = symplecticForm u v)
    (hmap : Φ '' Metric.ball (0 : SymplecticSpace ι) r ⊆ cylinder i₀ R) :
    r ≤ R := by
  set p : SymplecticSpace ι := Φ.symm (EuclideanSpace.single (Sum.inl i₀) (1 : ℝ)) with hp
  set q : SymplecticSpace ι := Φ.symm (EuclideanSpace.single (Sum.inr i₀) (1 : ℝ)) with hq
  have hΦp : Φ p = EuclideanSpace.single (Sum.inl i₀) (1 : ℝ) := Φ.apply_symm_apply _
  have hΦq : Φ q = EuclideanSpace.single (Sum.inr i₀) (1 : ℝ) := Φ.apply_symm_apply _
  -- the two coordinate functions of `Φ` in the cylinder plane
  have hcoord : ∀ x : SymplecticSpace ι, ‖x‖ < r →
      (symplecticForm x q) ^ 2 + (symplecticForm x p) ^ 2 < R ^ 2 := by
    intro x hx
    have hmem : Φ x ∈ cylinder i₀ R :=
      hmap ⟨x, by simpa [mem_ball_zero_iff] using hx, rfl⟩
    have h1 : (Φ x) (Sum.inl i₀) = symplecticForm x q := by
      rw [← symplecticForm_single_right (Φ x) i₀, ← hΦq, hsymp]
    have h2 : (Φ x) (Sum.inr i₀) = -symplecticForm x p := by
      rw [← symplecticForm_single_left (Φ x) i₀, ← hΦp, hsymp, symplecticForm_antisymm]
    have := hmem
    rw [cylinder, Set.mem_setOf_eq, h1, h2] at this
    simpa using this
  have hbq : r * ‖q‖ ≤ R := by
    refine radius_mul_norm_le r R hR q fun x hx => ?_
    have := hcoord x hx
    nlinarith [sq_nonneg (symplecticForm x p)]
  have hbp : r * ‖p‖ ≤ R := by
    refine radius_mul_norm_le r R hR p fun x hx => ?_
    have := hcoord x hx
    nlinarith [sq_nonneg (symplecticForm x q)]
  -- the symplectic form pairs `p` and `q` to `1`
  have hpq : symplecticForm p q = 1 := by
    rw [← hsymp p q, hΦp, hΦq]
    simp [EuclideanSpace.single_apply]
  have hcs : (1 : ℝ) ≤ ‖p‖ * ‖q‖ := by
    have := abs_symplecticForm_le p q
    rw [hpq] at this
    simpa using this
  nlinarith [norm_nonneg p, norm_nonneg q, mul_pos hr hr]

/-- Sharpness / non-vacuity: the identity (a linear symplectomorphism) does map the ball of
radius `r` into the cylinder of radius `r`, so the bound `r ≤ R` in `gromov_nonsqueezing`
cannot be improved. -/
theorem ball_subset_cylinder [DecidableEq ι] (i₀ : ι) (r : ℝ) (hr : 0 < r) :
    (LinearEquiv.refl ℝ (SymplecticSpace ι)) '' Metric.ball (0 : SymplecticSpace ι) r ⊆
      cylinder i₀ r := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_ball_zero_iff] at hx
  have hnorm : ‖x‖ ^ 2 = ∑ j : ι ⊕ ι, (x j) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [sq_abs]
  have hsub : ({Sum.inl i₀, Sum.inr i₀} : Finset (ι ⊕ ι)) ⊆ Finset.univ := Finset.subset_univ _
  have hpair : ∑ j ∈ ({Sum.inl i₀, Sum.inr i₀} : Finset (ι ⊕ ι)), (x j) ^ 2 =
      (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2 :=
    Finset.sum_pair (by simp)
  have hle : (x (Sum.inl i₀)) ^ 2 + (x (Sum.inr i₀)) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hnorm, ← hpair]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => sq_nonneg _
  have : ‖x‖ ^ 2 < r ^ 2 := by nlinarith [norm_nonneg x]
  simpa [cylinder] using lt_of_le_of_lt hle this

end Math2

