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

/-- The standard symplectic vector space `ℝ^{2(n+1)}`, realized as the Euclidean space with
index set `Fin (n+1) × Fin 2`: the index `(i, 0)` is the position coordinate `q i` and the
index `(i, 1)` is the momentum coordinate `p i`. -/
abbrev SympSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1) × Fin 2)

/-- The standard symplectic form `ω = ∑ i, dq i ∧ dp i` on `SympSpace n`. -/
def omegaForm {n : ℕ} (x y : SympSpace n) : ℝ :=
  ∑ i : Fin (n + 1), (x (i, 0) * y (i, 1) - x (i, 1) * y (i, 0))

/-- The standard complex structure `J` on `SympSpace n`, i.e. multiplication by `i`
(up to sign conventions): it sends `(q, p)` to `(-p, q)`. -/
def Jmap {n : ℕ} (x : SympSpace n) : SympSpace n :=
  WithLp.toLp 2 (fun z => if z.2 = 0 then -x (z.1, 1) else x (z.1, 0))

/-- The open ball of radius `r` in `SympSpace n`. -/
def symplecticBall (n : ℕ) (r : ℝ) : Set (SympSpace n) := Metric.ball 0 r

/-- The open symplectic cylinder of radius `R`, i.e. the set of points whose first pair of
conjugate coordinates `(q 0, p 0)` lies in the open disc of radius `R`. -/
def symplecticCylinder (n : ℕ) (R : ℝ) : Set (SympSpace n) :=
  {z : SympSpace n | (z (0, 0)) ^ 2 + (z (0, 1)) ^ 2 < R ^ 2}

/-! ### Basic properties of `ω` and `J` -/

lemma omegaForm_smul_right {n : ℕ} (c : ℝ) (x y : SympSpace n) :
    omegaForm x (c • y) = c * omegaForm x y := by
  simp only [omegaForm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

lemma inner_Jmap {n : ℕ} (x y : SympSpace n) : ⟪Jmap x, y⟫ = omegaForm x y := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [omegaForm, Fin.sum_univ_two, Jmap, WithLp.ofLp_toLp, RCLike.inner_apply,
    conj_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_num
  ring

lemma norm_Jmap {n : ℕ} (x : SympSpace n) : ‖Jmap x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Jmap, Fin.sum_univ_two]
  ring

/-- `ω (x, J x) = ‖x‖ ^ 2`: the symplectic form is tamed by the standard complex structure. -/
lemma omegaForm_Jmap_self {n : ℕ} (x : SympSpace n) : omegaForm x (Jmap x) = ‖x‖ ^ 2 := by
  have h : ⟪Jmap x, Jmap x⟫ = omegaForm x (Jmap x) := inner_Jmap x (Jmap x)
  rw [← h, real_inner_self_eq_norm_sq, norm_Jmap]

/-- Cauchy-Schwarz for the symplectic form: `|ω (x, y)| ≤ ‖x‖ * ‖y‖`. -/
lemma abs_omegaForm_le {n : ℕ} (x y : SympSpace n) : |omegaForm x y| ≤ ‖x‖ * ‖y‖ := by
  rw [← inner_Jmap]
  calc |⟪Jmap x, y⟫| ≤ ‖Jmap x‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [norm_Jmap]

/-! ### The two distinguished covectors -/

/-- The vector `v₀` characterized by `ω (v₀, z) = z (0, 0)`. -/
def vzero (n : ℕ) : SympSpace n := WithLp.toLp 2 (fun z => if z = (0, 1) then -1 else 0)

/-- The vector `v₁` characterized by `ω (v₁, z) = z (0, 1)`. -/
def vone (n : ℕ) : SympSpace n := WithLp.toLp 2 (fun z => if z = (0, 0) then 1 else 0)

lemma omegaForm_vzero {n : ℕ} (z : SympSpace n) : omegaForm (vzero n) z = z (0, 0) := by
  simp only [omegaForm, vzero, WithLp.ofLp_toLp]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · norm_num
  · intro b _ hb
    have h1 : ((b : Fin (n + 1)), (0 : Fin 2)) ≠ ((0 : Fin (n + 1)), (1 : Fin 2)) := by
      simp [Prod.ext_iff]
    have h2 : ((b : Fin (n + 1)), (1 : Fin 2)) ≠ ((0 : Fin (n + 1)), (1 : Fin 2)) := by
      simp [Prod.ext_iff, hb]
    simp [h1, h2]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma omegaForm_vone {n : ℕ} (z : SympSpace n) : omegaForm (vone n) z = z (0, 1) := by
  simp only [omegaForm, vone, WithLp.ofLp_toLp]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · norm_num
  · intro b _ hb
    have h1 : ((b : Fin (n + 1)), (0 : Fin 2)) ≠ ((0 : Fin (n + 1)), (0 : Fin 2)) := by
      simp [Prod.ext_iff, hb]
    have h2 : ((b : Fin (n + 1)), (1 : Fin 2)) ≠ ((0 : Fin (n + 1)), (0 : Fin 2)) := by
      simp [Prod.ext_iff]
    simp [h1, h2]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma omegaForm_vzero_vone {n : ℕ} : omegaForm (vzero n) (vone n) = 1 := by
  rw [omegaForm_vzero]
  simp [vone]

/-! ### Linear Gromov nonsqueezing -/

/--
**Gromov's nonsqueezing theorem** (the linear case).

If a linear symplectomorphism `Φ` of the standard symplectic vector space `ℝ^{2(n+1)}`
maps the open ball of radius `r` into the open symplectic cylinder of radius `R`
(the set of points whose first conjugate pair of coordinates has norm `< R`), then `r ≤ R`.

In other words, a symplectic map cannot squeeze a ball into a thinner cylinder: no
volume-preserving trickery in the remaining `2n` directions can help.
-/
theorem gromov_nonsqueezing {n : ℕ} {r R : ℝ} (hR : 0 ≤ R)
    (Φ : SympSpace n ≃ₗ[ℝ] SympSpace n)
    (hΦ : ∀ x y : SympSpace n, omegaForm (Φ x) (Φ y) = omegaForm x y)
    (hsub : Φ '' (symplecticBall n r) ⊆ symplecticCylinder n R) :
    r ≤ R := by
  by_contra hlt
  push_neg at hlt
  -- the two vectors representing the coordinate functionals `z ↦ (Φ z) (0, 0)` and
  -- `z ↦ (Φ z) (0, 1)` through the symplectic form
  set p : SympSpace n := Φ.symm (vzero n) with hp
  set q : SympSpace n := Φ.symm (vone n) with hq
  have hΦp : Φ p = vzero n := by simp [hp]
  have hΦq : Φ q = vone n := by simp [hq]
  have hrep0 : ∀ x : SympSpace n, omegaForm p x = (Φ x) (0, 0) := by
    intro x
    have := hΦ p x
    rw [hΦp, omegaForm_vzero] at this
    exact this.symm
  have hrep1 : ∀ x : SympSpace n, omegaForm q x = (Φ x) (0, 1) := by
    intro x
    have := hΦ q x
    rw [hΦq, omegaForm_vone] at this
    exact this.symm
  -- `ω (p, q) = 1`, hence `‖p‖ * ‖q‖ ≥ 1`
  have hpq : omegaForm p q = 1 := by
    have := hΦ p q
    rw [hΦp, hΦq, omegaForm_vzero_vone] at this
    exact this.symm
  have hnorm : 1 ≤ ‖p‖ * ‖q‖ := by
    have h := abs_omegaForm_le p q
    rw [hpq] at h
    simpa using h
  -- hence at least one of `p`, `q` has norm at least one
  have hcase : 1 ≤ ‖p‖ ∨ 1 ≤ ‖q‖ := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    have : ‖p‖ * ‖q‖ < 1 * 1 :=
      mul_lt_mul'' h1 h2 (norm_nonneg _) (norm_nonneg _)
    simp at this
    linarith
  -- a general contradiction mechanism: a vector `v` with `‖v‖ ≥ 1` whose associated
  -- coordinate functional is `ω (v, ·)` produces a point of the ball whose image leaves
  -- the cylinder
  have key : ∀ v : SympSpace n, 1 ≤ ‖v‖ →
      (∀ x : SympSpace n, omegaForm v x = (Φ x) (0, 0)) ∨
      (∀ x : SympSpace n, omegaForm v x = (Φ x) (0, 1)) → False := by
    intro v hv hrep
    have hvpos : (0 : ℝ) < ‖v‖ := lt_of_lt_of_le zero_lt_one hv
    set x : SympSpace n := (R / ‖v‖) • Jmap v with hx
    have hxnorm : ‖x‖ = R := by
      rw [hx, norm_smul, norm_Jmap, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      field_simp
    have hxball : x ∈ symplecticBall n r := by
      rw [symplecticBall, Metric.mem_ball, dist_zero_right, hxnorm]
      exact hlt
    have hmem : Φ x ∈ symplecticCylinder n R := hsub ⟨x, hxball, rfl⟩
    have hcyl : ((Φ x) (0, 0)) ^ 2 + ((Φ x) (0, 1)) ^ 2 < R ^ 2 := hmem
    have hval : omegaForm v x = R * ‖v‖ := by
      rw [hx, omegaForm_smul_right, omegaForm_Jmap_self]
      field_simp
    have hsq : R ^ 2 ≤ (R * ‖v‖) ^ 2 := by
      have h1 : R ^ 2 * 1 ≤ R ^ 2 * ‖v‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
        nlinarith
      nlinarith
    rcases hrep with h | h
    · have : (Φ x) (0, 0) = R * ‖v‖ := by rw [← h x, hval]
      rw [this] at hcyl
      nlinarith [sq_nonneg ((Φ x) (0, 1))]
    · have : (Φ x) (0, 1) = R * ‖v‖ := by rw [← h x, hval]
      rw [this] at hcyl
      nlinarith [sq_nonneg ((Φ x) (0, 0))]
  rcases hcase with h | h
  · exact key p h (Or.inl hrep0)
  · exact key q h (Or.inr hrep1)

end Math2

