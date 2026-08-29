import Mathlib
/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators RealInnerProductSpace

namespace Math2

/-- The standard symplectic vector space `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2`: the pair `(i, 0), (i, 1)` is the `i`-th conjugate coordinate pair. -/
abbrev SympSpace (n : ℕ) : Type := EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard symplectic form on `ℝ^{2n}`. -/
def omegaForm {n : ℕ} (u v : SympSpace n) : ℝ :=
  ∑ i : Fin n, (u (i, 0) * v (i, 1) - u (i, 1) * v (i, 0))

/-- A linear map of `ℝ^{2n}` is symplectic if it preserves the standard symplectic form. -/
def IsLinearSymplectic {n : ℕ} (A : SympSpace n →ₗ[ℝ] SympSpace n) : Prop :=
  ∀ u v : SympSpace n, omegaForm (A u) (A v) = omegaForm u v

/-- The symplectic cylinder of radius `R` over the `j`-th conjugate coordinate plane:
the set of points whose `j`-th conjugate coordinate pair has norm at most `R`. -/
def Cylinder {n : ℕ} (j : Fin n) (R : ℝ) : Set (SympSpace n) :=
  {z | z (j, 0) ^ 2 + z (j, 1) ^ 2 ≤ R ^ 2}

/-- The standard complex structure `J` on `ℝ^{2n}`. -/
def Jmap {n : ℕ} (u : SympSpace n) : SympSpace n :=
  WithLp.toLp 2 (fun p : Fin n × Fin 2 => if p.2 = 0 then -u (p.1, 1) else u (p.1, 0))

@[simp] lemma Jmap_apply_zero {n : ℕ} (u : SympSpace n) (i : Fin n) :
    Jmap u (i, 0) = -u (i, 1) := rfl

@[simp] lemma Jmap_apply_one {n : ℕ} (u : SympSpace n) (i : Fin n) :
    Jmap u (i, 1) = u (i, 0) := rfl

lemma Jmap_neg {n : ℕ} (u : SympSpace n) : Jmap (-u) = -Jmap u := by
  ext p
  obtain ⟨i, a⟩ := p
  fin_cases a <;> simp [Jmap]

lemma Jmap_Jmap {n : ℕ} (u : SympSpace n) : Jmap (Jmap u) = -u := by
  ext p
  obtain ⟨i, a⟩ := p
  fin_cases a <;> simp

lemma norm_Jmap {n : ℕ} (u : SympSpace n) : ‖Jmap u‖ = ‖u‖ := by
  simp only [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Fin.sum_univ_two]
  ring

lemma omegaForm_eq_inner {n : ℕ} (u v : SympSpace n) : omegaForm u v = ⟪Jmap u, v⟫ := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, omegaForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Fin.sum_univ_two]
  ring

lemma omegaForm_Jmap {n : ℕ} (u v : SympSpace n) :
    omegaForm (Jmap u) (Jmap v) = omegaForm u v := by
  simp only [omegaForm, Jmap_apply_zero, Jmap_apply_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma omegaForm_neg_neg {n : ℕ} (u v : SympSpace n) :
    omegaForm (-u) (-v) = omegaForm u v := by
  simp only [omegaForm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

/-- The symplectic form is nondegenerate. -/
lemma eq_zero_of_omegaForm_eq_zero {n : ℕ} {x : SympSpace n}
    (h : ∀ y : SympSpace n, omegaForm x y = 0) : x = 0 := by
  ext p
  obtain ⟨i, a⟩ := p
  fin_cases a
  · have := h (EuclideanSpace.single (i, 1) (1 : ℝ))
    simpa [omegaForm, EuclideanSpace.single_apply, Prod.ext_iff, Finset.sum_ite_eq'] using this
  · have := h (EuclideanSpace.single (i, 0) (1 : ℝ))
    simp only [omegaForm, EuclideanSpace.single_apply, Prod.ext_iff] at this
    simpa [Finset.sum_ite_eq'] using this

lemma injective_of_symplectic {n : ℕ} {A : SympSpace n →ₗ[ℝ] SympSpace n}
    (hA : IsLinearSymplectic A) : Function.Injective A := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine eq_zero_of_omegaForm_eq_zero fun y => ?_
  rw [← hA x y, hx]
  simp [omegaForm]

lemma omegaForm_single {n : ℕ} (j : Fin n) :
    omegaForm (EuclideanSpace.single (j, 0) (1 : ℝ)) (EuclideanSpace.single (j, 1) (1 : ℝ))
      = 1 := by
  simp [omegaForm, EuclideanSpace.single_apply, Prod.ext_iff, Finset.sum_ite_eq']

/-- **Gromov nonsqueezing (linear case).**  If a linear symplectomorphism of the standard
symplectic space `ℝ^{2n}` maps the closed ball of radius `r` centred at the origin into the
symplectic cylinder of radius `R` over a conjugate coordinate plane, then `r ≤ R`.

(The full Gromov nonsqueezing theorem, for arbitrary smooth symplectic embeddings, requires the
theory of pseudoholomorphic curves; the statement proved here is the classical linear case.) -/
theorem gromov_nonsqueezing {n : ℕ} (j : Fin n) (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (A : SympSpace n →ₗ[ℝ] SympSpace n) (hA : IsLinearSymplectic A)
    (hsub : A '' Metric.closedBall (0 : SympSpace n) r ⊆ Cylinder j R) :
    r ≤ R := by
  classical
  -- `A` is bijective.
  have hinj : Function.Injective A := injective_of_symplectic hA
  have hsurj : Function.Surjective A := LinearMap.injective_iff_surjective.mp hinj
  set e : SympSpace n := EuclideanSpace.single (j, 0) (1 : ℝ) with he
  set f : SympSpace n := EuclideanSpace.single (j, 1) (1 : ℝ) with hf
  obtain ⟨c, hc⟩ := hsurj (-(Jmap e))
  obtain ⟨d, hd⟩ := hsurj (-(Jmap f))
  set a : SympSpace n := Jmap c with ha_def
  set b : SympSpace n := Jmap d with hb_def
  -- the coordinate functionals of `A` on the `j`-th plane are given by `a` and `b`
  have ha : ∀ x : SympSpace n, ⟪a, x⟫ = A x (j, 0) := by
    intro x
    have h1 : ⟪a, x⟫ = omegaForm c x := (omegaForm_eq_inner c x).symm
    rw [h1, ← hA c x, hc, omegaForm_eq_inner, Jmap_neg, Jmap_Jmap, neg_neg]
    rw [PiLp.inner_apply]
    simp [he, EuclideanSpace.single_apply, Finset.sum_ite_eq']
  have hb : ∀ x : SympSpace n, ⟪b, x⟫ = A x (j, 1) := by
    intro x
    have h1 : ⟪b, x⟫ = omegaForm d x := (omegaForm_eq_inner d x).symm
    rw [h1, ← hA d x, hd, omegaForm_eq_inner, Jmap_neg, Jmap_Jmap, neg_neg]
    rw [PiLp.inner_apply]
    simp [hf, EuclideanSpace.single_apply, Finset.sum_ite_eq']
  -- `a` and `b` span a symplectic plane
  have hab : omegaForm a b = 1 := by
    rw [ha_def, hb_def, omegaForm_Jmap, ← hA c d, hc, hd, omegaForm_neg_neg, omegaForm_Jmap,
      he, hf, omegaForm_single]
  have hCS : 1 ≤ ‖a‖ * ‖b‖ := by
    have h1 : (1 : ℝ) = ⟪Jmap a, b⟫ := by rw [← omegaForm_eq_inner, hab]
    calc (1 : ℝ) = ⟪Jmap a, b⟫ := h1
      _ ≤ ‖Jmap a‖ * ‖b‖ := real_inner_le_norm _ _
      _ = ‖a‖ * ‖b‖ := by rw [norm_Jmap]
  have hapos : 0 < ‖a‖ := by
    rcases (norm_nonneg a).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hCS; simp at hCS; linarith
  have hbpos : 0 < ‖b‖ := by
    rcases (norm_nonneg b).lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hCS; simp at hCS; linarith
  -- the two coordinate functionals are bounded by `R` on the ball of radius `r`
  have key : ∀ v : SympSpace n, 0 < ‖v‖ → (∀ x : SympSpace n, ⟪v, x⟫ = A x (j, 0)) ∨
      (∀ x : SympSpace n, ⟪v, x⟫ = A x (j, 1)) → r * ‖v‖ ≤ R := by
    intro v hv hcase
    set x : SympSpace n := (r / ‖v‖) • v with hx
    have hxmem : x ∈ Metric.closedBall (0 : SympSpace n) r := by
      rw [mem_closedBall_zero_iff, hx, norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact le_of_eq (div_mul_cancel₀ r hv.ne')
    have hinner : ⟪v, x⟫ = r * ‖v‖ := by
      rw [hx, real_inner_smul_right, real_inner_self_eq_norm_mul_norm]
      field_simp
    have hcyl : (A x (j, 0)) ^ 2 + (A x (j, 1)) ^ 2 ≤ R ^ 2 :=
      hsub ⟨x, hxmem, rfl⟩
    have hsq : (r * ‖v‖) ^ 2 ≤ R ^ 2 := by
      rcases hcase with hcase | hcase
      · rw [← hcase x, hinner] at hcyl; nlinarith [sq_nonneg (A x (j, 1))]
      · rw [← hcase x, hinner] at hcyl; nlinarith [sq_nonneg (A x (j, 0))]
    nlinarith [mul_nonneg hr hv.le]
  have hna : r * ‖a‖ ≤ R := key a hapos (Or.inl ha)
  have hnb : r * ‖b‖ ≤ R := key b hbpos (Or.inr hb)
  nlinarith [mul_pos hapos hbpos, sq_nonneg r]

/-! ### Sanity checks: the hypotheses of `gromov_nonsqueezing` are satisfiable -/

/-- The identity is a linear symplectomorphism. -/
example : IsLinearSymplectic (LinearMap.id : SympSpace 1 →ₗ[ℝ] SympSpace 1) := fun _ _ => rfl

/-- The identity squeezes the unit ball of `ℝ²` into the cylinder of radius `1`,
so the hypotheses of `gromov_nonsqueezing` are non-vacuous. -/
example : (LinearMap.id : SympSpace 1 →ₗ[ℝ] SympSpace 1) ''
    Metric.closedBall (0 : SympSpace 1) 1 ⊆ Cylinder 0 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq] at hx
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_two, Real.norm_eq_abs,
    sq_abs] at hx
  have h0 : (0:ℝ) ≤ x (0, 0) ^ 2 + x (0, 1) ^ 2 := by positivity
  have hsq := Real.sq_sqrt h0
  show (x (0, 0)) ^ 2 + (x (0, 1)) ^ 2 ≤ (1 : ℝ) ^ 2
  nlinarith [Real.sqrt_nonneg (x (0, 0) ^ 2 + x (0, 1) ^ 2)]

end Math2

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

