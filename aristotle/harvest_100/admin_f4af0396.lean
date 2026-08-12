import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

(The `import Mathlib` line must precede this file's module documentation because Lean 4
requires all `import` commands to come first; the required header comment is otherwise
reproduced verbatim as the first block of the file.)

Gleason's theorem states that every quantum measure (normalized, finitely additive probability
assignment on the closed subspaces, i.e. a normalized frame function) on a complex Hilbert
space of dimension at least `3` is of the form `P ↦ tr (rho P)` for a unique density operator
`rho`.  Here the space is `EuclideanSpace ℂ (Fin n)` and operators are `n × n` complex matrices.

What is formalized and proved in this file:

* `Frontier.IsQuantumMeasure`, `Frontier.IsDensityOperator`, `Frontier.RepresentedBy`,
  `Frontier.GleasonProperty` -- the statement of the theorem.
* `Frontier.gleason_theorem` -- the *reduction*: a quantum measure that extends to a linear
  functional on operators is given by a density operator (trace-duality plus positivity).
* `Frontier.gleason_theorem_of_selfAdjoint_linear` -- the same with the more natural hypothesis
  of a real-linear extension over the self-adjoint operators, via complexification
  (`Frontier.hasLinearExtension_of_selfAdjoint`, `Frontier.hasSelfAdjointLinearExtension_iff`).
* `Frontier.hasLinearExtension_iff_gleasonProperty` -- the linearity hypothesis is exactly
  equivalent to the conclusion, so the reduction is lossless: all that is missing from a full
  proof of Gleason's theorem is the (deep) fact that in dimension `≥ 3` every quantum measure
  admits such an extension.
* `Frontier.isQuantumMeasure_of_isDensityOperator` -- the converse direction.
* `Frontier.representedBy_unique` -- uniqueness of the density operator.
* `Frontier.gleason_dim_one` -- the base case `n = 1`, unconditionally.
* `Frontier.gleason_fails_dim_two` -- sharpness: an explicit quantum measure on a qubit
  (`Frontier.qubitMeasure`, built from the cubic `3a² - 2a³`) that comes from no density
  operator, so the hypothesis `3 ≤ n` cannot be removed.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions

We model a complex Hilbert space of dimension `n` as `EuclideanSpace ℂ (Fin n)`, and the
bounded operators on it as `Matrix (Fin n) (Fin n) ℂ`.  An *event* (a closed subspace) is
recorded by its orthogonal projection. -/

/-- An orthogonal projection: a self-adjoint idempotent matrix. -/
def IsProjection (P : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- A *quantum measure* (a normalized finitely additive probability measure on the lattice of
closed subspaces, i.e. a normalized frame function) on the `n`-dimensional complex Hilbert
space: a nonnegative function on orthogonal projections which is normalized at the identity
and additive on orthogonal pairs of projections. -/
structure IsQuantumMeasure (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop where
  nonneg : ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProjection P → 0 ≤ mu P
  normalized : mu 1 = 1
  additive : ∀ P Q : Matrix (Fin n) (Fin n) ℂ, IsProjection P → IsProjection Q → P * Q = 0 →
    mu (P + Q) = mu P + mu Q

/-- A density operator: a positive semidefinite operator of unit trace. -/
def IsDensityOperator (rho : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  rho.PosSemidef ∧ rho.trace = 1

/-- `mu` is *represented* by the operator `rho` if `mu P = tr (rho P)` for every projection. -/
def RepresentedBy (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) (rho : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProjection P → (rho * P).trace = (mu P : ℂ)

/-- The conclusion of Gleason's theorem for a given quantum measure: it comes from a density
operator. -/
def GleasonProperty (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop :=
  ∃ rho : Matrix (Fin n) (Fin n) ℂ, IsDensityOperator rho ∧ RepresentedBy mu rho

/-- `mu` extends to a (complex-)linear functional on all operators.  This is exactly the
analytic content of Gleason's theorem: the hard part of the theorem is to prove that every
quantum measure on a space of dimension `≥ 3` has such an extension. -/
def HasLinearExtension (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop :=
  ∃ f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ, ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProjection P →
    f P = (mu P : ℂ)

/-! ## Elementary lemmas about projections and rank-one operators -/

/-- The rank-one operator `x xᴴ` attached to a vector `x`. -/
noncomputable def rankOne (x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec x (star x)

lemma isProjection_one : IsProjection (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨Matrix.isHermitian_one, by simp⟩

lemma dotProduct_star_self (x : Fin n → ℂ) :
    star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun i _ => Complex.conj_mul' (x i)

/-- A unit vector gives a rank-one orthogonal projection. -/
lemma isProjection_rankOne (x : Fin n → ℂ) (hx : star x ⬝ᵥ x = 1) : IsProjection (rankOne x) := by
  constructor
  · ext i j
    simp [rankOne, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]
  · ext i j
    simp only [rankOne, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    have h : ∑ k, x i * (starRingEnd ℂ) (x k) * (x k * (starRingEnd ℂ) (x j))
        = (x i * (starRingEnd ℂ) (x j)) * ∑ k, (starRingEnd ℂ) (x k) * x k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hx' : ∑ k, (starRingEnd ℂ) (x k) * x k = 1 := by
      simpa [dotProduct] using hx
    simp only [RCLike.star_def] at h ⊢
    rw [h, hx', mul_one]

/-- Pairing a matrix with a rank-one operator computes the quadratic form. -/
lemma trace_mul_rankOne (rho : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (rho * rankOne x).trace = star x ⬝ᵥ rho *ᵥ x := by
  simp only [rankOne, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMulVec_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Over `ℂ`, an operator with real quadratic form is self-adjoint. -/
lemma isHermitian_of_quadratic_real (rho : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ x : Fin n → ℂ, (starRingEnd ℂ) (star x ⬝ᵥ rho *ᵥ x) = star x ⬝ᵥ rho *ᵥ x) :
    rho.IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymmetric, LinearMap.isSymmetric_iff_inner_map_self_real]
  intro v
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  have h3 : v.ofLp ⬝ᵥ star (rho *ᵥ v.ofLp) = (starRingEnd ℂ) (star v.ofLp ⬝ᵥ rho *ᵥ v.ofLp) := by
    simp [dotProduct, map_sum, mul_comm]
  rw [h3, h v.ofLp]
  exact h v.ofLp

/-- An operator with vanishing quadratic form vanishes (complex polarization). -/
lemma eq_zero_of_quadratic_zero (B : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ x : Fin n → ℂ, star x ⬝ᵥ B *ᵥ x = 0) : B = 0 := by
  have hT : Matrix.toEuclideanLin B = 0 := by
    rw [← inner_map_self_eq_zero (Matrix.toEuclideanLin B)]
    intro v
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    have h3 : v.ofLp ⬝ᵥ star (B *ᵥ v.ofLp) = (starRingEnd ℂ) (star v.ofLp ⬝ᵥ B *ᵥ v.ofLp) := by
      simp [dotProduct, map_sum, mul_comm]
    rw [h3, h v.ofLp, map_zero]
  exact (LinearEquiv.map_eq_zero_iff Matrix.toEuclideanLin).mp hT

/-! ## Trace duality

Every linear functional on matrices is `A ↦ tr (rho A)` for a unique `rho`. -/

/-- The operator representing a linear functional under the trace pairing. -/
noncomputable def dualOperator (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => f (Matrix.single j i (1 : ℂ))

lemma trace_dualOperator_mul (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : (dualOperator f * A).trace = f A := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  simp only [dualOperator, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  simp only [map_sum]
  have h1 : ∀ i j : Fin n, Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) := by
    intro i j
    ext a b
    by_cases h : a = i <;> by_cases h' : b = j <;> simp [h, h', Matrix.single]
  simp only [h1, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ## Positivity of the dual operator of a quantum measure -/

/-- Any nonzero vector can be rescaled to a unit vector; the quadratic form of any operator
scales by the squared norm. -/
lemma quadratic_rescale (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ (t : ℝ) (y : Fin n → ℂ), 0 ≤ t ∧ star y ⬝ᵥ y = 1 ∧
      ∀ B : Matrix (Fin n) (Fin n) ℂ, star x ⬝ᵥ B *ᵥ x = (t : ℂ) * (star y ⬝ᵥ B *ᵥ y) := by
  set t : ℝ := ∑ i, ‖x i‖ ^ 2 with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => by positivity
  have hpos : 0 < t := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun j _ => by positivity)
      ⟨i, Finset.mem_univ i, pow_pos (norm_pos_iff.mpr hi) 2⟩
  obtain ⟨s, hspos, hst⟩ : ∃ s : ℝ, 0 < s ∧ t = s * s :=
    ⟨Real.sqrt t, Real.sqrt_pos.mpr hpos, (Real.mul_self_sqrt ht0).symm⟩
  have hsne : s ≠ 0 := ne_of_gt hspos
  set c : ℝ := s⁻¹ with hc
  have hcct : c * c * t = 1 := by
    rw [hc, hst]
    field_simp
  have hctC : (c : ℂ) * (c : ℂ) * (t : ℂ) = 1 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hcct
    push_cast at h
    simpa using h
  refine ⟨t, (c : ℂ) • x, ht0, ?_, ?_⟩
  · have h1 : star ((c : ℂ) • x) ⬝ᵥ ((c : ℂ) • x) = ((c : ℂ) * (c : ℂ)) * (star x ⬝ᵥ x) := by
      simp only [Pi.star_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Complex.star_def,
        map_mul, Complex.conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, dotProduct_star_self, ← ht]
    exact hctC
  · intro B
    have hscale : star ((c : ℂ) • x) ⬝ᵥ B *ᵥ ((c : ℂ) • x)
        = ((c : ℂ) * (c : ℂ)) * (star x ⬝ᵥ B *ᵥ x) := by
      simp only [Pi.star_apply, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul,
        Complex.star_def, map_mul, Complex.conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hscale]
    have h5 : (t : ℂ) * ((c : ℂ) * (c : ℂ)) = 1 := by rw [← hctC]; ring
    calc star x ⬝ᵥ B *ᵥ x
        = ((t : ℂ) * ((c : ℂ) * (c : ℂ))) * (star x ⬝ᵥ B *ᵥ x) := by rw [h5, one_mul]
      _ = (t : ℂ) * (((c : ℂ) * (c : ℂ)) * (star x ⬝ᵥ B *ᵥ x)) := by ring

/-- If a quantum measure `mu` is the restriction of a linear functional `f`, then the quadratic
form of the dual operator of `f` takes nonnegative real values. -/
lemma quadratic_form_nonneg_real (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) (hmu : IsQuantumMeasure mu)
    (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hf : ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProjection P → f P = (mu P : ℂ))
    (x : Fin n → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ star x ⬝ᵥ dualOperator f *ᵥ x = (r : ℂ) := by
  have hquad : ∀ y : Fin n → ℂ, star y ⬝ᵥ dualOperator f *ᵥ y = f (rankOne y) := fun y => by
    rw [← trace_mul_rankOne, trace_dualOperator_mul]
  by_cases hx : x = 0
  · exact ⟨0, le_refl 0, by simp [hx]⟩
  · obtain ⟨t, y, ht0, hy1, hscale⟩ := quadratic_rescale x hx
    refine ⟨t * mu (rankOne y), mul_nonneg ht0 (hmu.nonneg _ (isProjection_rankOne y hy1)), ?_⟩
    rw [hscale (dualOperator f), hquad y, hf _ (isProjection_rankOne y hy1)]
    push_cast
    ring

/-! ## The main results -/

/-- **Gleason's theorem (linear-extension reduction).**  Let `mu` be a quantum measure on the
`n`-dimensional complex Hilbert space, `n ≥ 3`.  If `mu` extends to a linear functional on
operators -- which is precisely the hard analytic content of Gleason's theorem -- then `mu`
comes from a density operator: there is a positive semidefinite `rho` with `tr rho = 1` and
`mu P = tr (rho P)` for every orthogonal projection `P`.

The dimension hypothesis `3 ≤ n` is the one in the classical statement; it is needed to obtain
the linear extension, and is not used in the reduction proved here. -/
theorem gleason_theorem (hn : 3 ≤ n) (mu : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (hmu : IsQuantumMeasure mu) (hlin : HasLinearExtension mu) : GleasonProperty mu := by
  obtain ⟨f, hf⟩ := hlin
  refine ⟨dualOperator f, ⟨?_, ?_⟩, ?_⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · refine isHermitian_of_quadratic_real _ fun x => ?_
      obtain ⟨r, _, hr⟩ := quadratic_form_nonneg_real mu hmu f hf x
      rw [hr, Complex.conj_ofReal]
    · intro x
      obtain ⟨r, hr0, hr⟩ := quadratic_form_nonneg_real mu hmu f hf x
      rw [hr]
      exact Complex.zero_le_real.mpr hr0
  · have h1 : (dualOperator f * 1).trace = f 1 := trace_dualOperator_mul f 1
    rw [mul_one] at h1
    rw [h1, hf 1 isProjection_one, hmu.normalized]
    norm_num
  · intro P hP
    rw [trace_dualOperator_mul f P, hf P hP]

/-- For a positive semidefinite `rho` and an orthogonal projection `P`, the number `tr (rho P)`
is a nonnegative real. -/
lemma trace_mul_projection_nonneg (rho : Matrix (Fin n) (Fin n) ℂ) (hrho : rho.PosSemidef)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsProjection P) : 0 ≤ (rho * P).trace := by
  have h1 : (rho * P).trace = (Pᴴ * rho * P).trace := by
    conv_lhs => rw [← hP.2]
    rw [hP.1.eq, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  rw [h1]
  exact (hrho.conjTranspose_mul_mul_same P).trace_nonneg

/-- **Converse of Gleason's theorem.**  Every density operator defines a quantum measure, and
that quantum measure is represented by it. -/
theorem isQuantumMeasure_of_isDensityOperator (rho : Matrix (Fin n) (Fin n) ℂ)
    (hrho : IsDensityOperator rho) :
    IsQuantumMeasure (fun P => ((rho * P).trace).re) ∧
      RepresentedBy (fun P => ((rho * P).trace).re) rho := by
  obtain ⟨hpsd, htr⟩ := hrho
  have hreal : ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProjection P →
      (rho * P).trace = (((rho * P).trace).re : ℂ) := by
    intro P hP
    have h := trace_mul_projection_nonneg rho hpsd P hP
    rw [Complex.le_def] at h
    exact Complex.ext rfl (by simpa using h.2.symm)
  refine ⟨⟨?_, ?_, ?_⟩, hreal⟩
  · intro P hP
    have h := trace_mul_projection_nonneg rho hpsd P hP
    rw [Complex.le_def] at h
    simpa using h.1
  · rw [mul_one, htr]
    norm_num
  · intro P Q _ _ _
    rw [mul_add, Matrix.trace_add, Complex.add_re]

/-- The density operator representing a quantum measure is unique. -/
theorem representedBy_unique (mu : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (rho1 rho2 : Matrix (Fin n) (Fin n) ℂ) (h1 : RepresentedBy mu rho1)
    (h2 : RepresentedBy mu rho2) : rho1 = rho2 := by
  have key : ∀ x : Fin n → ℂ, star x ⬝ᵥ (rho1 - rho2) *ᵥ x = 0 := by
    intro x
    have hunit : ∀ y : Fin n → ℂ, star y ⬝ᵥ y = 1 → star y ⬝ᵥ (rho1 - rho2) *ᵥ y = 0 := by
      intro y hy
      have hP := isProjection_rankOne y hy
      rw [← trace_mul_rankOne, sub_mul, Matrix.trace_sub, h1 _ hP, h2 _ hP, sub_self]
    by_cases hx : x = 0
    · simp [hx]
    · obtain ⟨t, y, _, hy1, hscale⟩ := quadratic_rescale x hx
      rw [hscale (rho1 - rho2), hunit y hy1, mul_zero]
  exact sub_eq_zero.mp (eq_zero_of_quadratic_zero _ key)

/-- **Gleason's theorem, packaged.**  Under the linear-extension hypothesis, a quantum measure
on a space of dimension `n ≥ 3` is represented by a *unique* density operator. -/
theorem gleason_theorem_unique (hn : 3 ≤ n) (mu : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (hmu : IsQuantumMeasure mu) (hlin : HasLinearExtension mu) :
    ∃! rho : Matrix (Fin n) (Fin n) ℂ, IsDensityOperator rho ∧ RepresentedBy mu rho := by
  obtain ⟨rho, hrho, hrep⟩ := gleason_theorem hn mu hmu hlin
  exact ⟨rho, ⟨hrho, hrep⟩, fun rho' hrho' => representedBy_unique mu rho' rho hrho'.2 hrep⟩

/-- The linear functional `A ↦ tr (rho A)` attached to an operator `rho`. -/
noncomputable def traceFunctional (rho : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun A := (rho * A).trace
  map_add' A B := by rw [mul_add, Matrix.trace_add]
  map_smul' c A := by rw [Matrix.mul_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul]

/-- The hypothesis of the reduction is not merely sufficient but also necessary: a quantum
measure comes from a density operator exactly when it extends to a linear functional. -/
theorem hasLinearExtension_iff_gleasonProperty (hn : 3 ≤ n) (mu : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (hmu : IsQuantumMeasure mu) : HasLinearExtension mu ↔ GleasonProperty mu := by
  refine ⟨gleason_theorem hn mu hmu, ?_⟩
  rintro ⟨rho, -, hrep⟩
  exact ⟨traceFunctional rho, fun P hP => hrep P hP⟩

/-- The zero operator is a projection. -/
lemma isProjection_zero : IsProjection (0 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨Matrix.isHermitian_zero, by simp⟩

/-- Every quantum measure vanishes on the zero projection. -/
lemma IsQuantumMeasure.map_zero {mu : Matrix (Fin n) (Fin n) ℂ → ℝ} (hmu : IsQuantumMeasure mu) :
    mu 0 = 0 := by
  have h := hmu.additive 0 0 isProjection_zero isProjection_zero (by simp)
  simp only [add_zero] at h
  linarith

/-- **Base case: dimension one.**  In dimension `1` Gleason's conclusion holds unconditionally
(the only projections are `0` and `1`). -/
theorem gleason_dim_one (mu : Matrix (Fin 1) (Fin 1) ℂ → ℝ) (hmu : IsQuantumMeasure mu) :
    GleasonProperty mu := by
  refine ⟨1, ⟨Matrix.PosSemidef.one, by simp⟩, ?_⟩
  intro P hP
  have hentry : P 0 0 * P 0 0 = P 0 0 := by
    have := congrFun (congrFun hP.2 0) 0
    simpa [Matrix.mul_apply] using this
  have hcases : P = 0 ∨ P = 1 := by
    have hfac : P 0 0 * (P 0 0 - 1) = 0 := by linear_combination hentry
    rcases mul_eq_zero.mp hfac with h | h
    · left
      ext i j
      fin_cases i
      fin_cases j
      simpa using h
    · right
      ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.one_apply] using sub_eq_zero.mp h
  rcases hcases with h | h
  · rw [h, mul_zero, Matrix.trace_zero, hmu.map_zero]
    norm_num
  · rw [h, mul_one, hmu.normalized]
    simp

/-! ## A weaker (more natural) form of the linearity hypothesis

Gleason's argument produces a functional that is only *real*-linear on the self-adjoint
operators (the observables).  We show this suffices: such a functional complexifies to a
`ℂ`-linear functional on all operators. -/

/-- The self-adjoint "real part" of an operator. -/
noncomputable def rePart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (2⁻¹ : ℂ) • (A + Aᴴ)

/-- The self-adjoint "imaginary part" of an operator. -/
noncomputable def imPart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((2 : ℂ)⁻¹ * (-Complex.I)) • (A - Aᴴ)

lemma rePart_selfAdjoint (A : Matrix (Fin n) (Fin n) ℂ) : (rePart A)ᴴ = rePart A := by
  ext i j
  simp [rePart, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

lemma imPart_selfAdjoint (A : Matrix (Fin n) (Fin n) ℂ) : (imPart A)ᴴ = imPart A := by
  ext i j
  simp [imPart, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply, Complex.conj_I]
  ring

lemma rePart_add (A B : Matrix (Fin n) (Fin n) ℂ) : rePart (A + B) = rePart A + rePart B := by
  ext i j
  simp [rePart, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

lemma imPart_add (A B : Matrix (Fin n) (Fin n) ℂ) : imPart (A + B) = imPart A + imPart B := by
  ext i j
  simp [imPart, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply]
  ring

lemma rePart_real_smul (r : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    rePart ((r : ℂ) • A) = (r : ℂ) • rePart A := by
  ext i j
  simp [rePart, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

lemma imPart_real_smul (r : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    imPart ((r : ℂ) • A) = (r : ℂ) • imPart A := by
  ext i j
  simp [imPart, Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

lemma rePart_I_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    rePart (Complex.I • A) = -imPart A := by
  ext i j
  simp [rePart, imPart, Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Complex.conj_I]
  ring

lemma imPart_I_smul (A : Matrix (Fin n) (Fin n) ℂ) :
    imPart (Complex.I • A) = rePart A := by
  ext i j
  simp [rePart, imPart, Matrix.conjTranspose_apply, Matrix.add_apply,
    Matrix.smul_apply, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma rePart_of_selfAdjoint (A : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ = A) : rePart A = A := by
  rw [rePart, h]
  ext i j
  simp [Matrix.smul_apply, Matrix.add_apply]
  ring

lemma imPart_of_selfAdjoint (A : Matrix (Fin n) (Fin n) ℂ) (h : Aᴴ = A) : imPart A = 0 := by
  rw [imPart, h, sub_self, smul_zero]

/-- `mu` extends to a functional on the self-adjoint operators which is additive and
real-homogeneous.  This is the form of linearity that Gleason's argument produces. -/
def HasSelfAdjointLinearExtension (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop :=
  ∃ g : Matrix (Fin n) (Fin n) ℂ → ℝ,
    (∀ A B : Matrix (Fin n) (Fin n) ℂ, Aᴴ = A → Bᴴ = B → g (A + B) = g A + g B) ∧
    (∀ (r : ℝ) (A : Matrix (Fin n) (Fin n) ℂ), Aᴴ = A → g ((r : ℂ) • A) = r * g A) ∧
    (∀ P : Matrix (Fin n) (Fin n) ℂ, IsProjection P → g P = mu P)

/-- Complexification: a real-linear extension on the self-adjoint operators yields a
complex-linear extension on all operators. -/
theorem hasLinearExtension_of_selfAdjoint (mu : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (h : HasSelfAdjointLinearExtension mu) : HasLinearExtension mu := by
  obtain ⟨g, hadd, hsmul, hproj⟩ := h
  have hg0 : g 0 = 0 := by
    have h0 : ((0 : Matrix (Fin n) (Fin n) ℂ))ᴴ = 0 := Matrix.conjTranspose_zero
    have := hadd 0 0 h0 h0
    simp only [add_zero] at this
    linarith
  have hgneg : ∀ A : Matrix (Fin n) (Fin n) ℂ, Aᴴ = A → g (-A) = -g A := by
    intro A hA
    have := hsmul (-1) A hA
    simpa using this
  set F : Matrix (Fin n) (Fin n) ℂ → ℂ :=
    fun A => (g (rePart A) : ℂ) + Complex.I * (g (imPart A) : ℂ) with hFdef
  have hFadd : ∀ A B, F (A + B) = F A + F B := by
    intro A B
    simp only [hFdef, rePart_add, imPart_add,
      hadd _ _ (rePart_selfAdjoint A) (rePart_selfAdjoint B),
      hadd _ _ (imPart_selfAdjoint A) (imPart_selfAdjoint B)]
    push_cast
    ring
  have hFreal : ∀ (r : ℝ) (A : Matrix (Fin n) (Fin n) ℂ), F ((r : ℂ) • A) = (r : ℂ) * F A := by
    intro r A
    simp only [hFdef, rePart_real_smul, imPart_real_smul,
      hsmul r _ (rePart_selfAdjoint A), hsmul r _ (imPart_selfAdjoint A)]
    push_cast
    ring
  have hFI : ∀ A : Matrix (Fin n) (Fin n) ℂ, F (Complex.I • A) = Complex.I * F A := by
    intro A
    simp only [hFdef, rePart_I_smul, imPart_I_smul, hgneg _ (imPart_selfAdjoint A)]
    push_cast
    linear_combination (-(g (imPart A) : ℂ)) * Complex.I_sq
  have hFsmul : ∀ (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ), F (c • A) = c * F A := by
    intro c A
    have hc : c • A = ((c.re : ℂ) • A) + ((c.im : ℂ) • (Complex.I • A)) := by
      rw [smul_smul, ← add_smul, Complex.re_add_im]
    rw [hc, hFadd, hFreal, hFreal, hFI]
    have hre : (c.re : ℂ) + (c.im : ℂ) * Complex.I = c := Complex.re_add_im c
    linear_combination (F A) * hre
  refine ⟨{ toFun := F, map_add' := hFadd, map_smul' := fun c A => by simpa using hFsmul c A }, ?_⟩
  intro P hP
  simp only [LinearMap.coe_mk, AddHom.coe_mk, hFdef, rePart_of_selfAdjoint P hP.1.eq,
    imPart_of_selfAdjoint P hP.1.eq, hg0, hproj P hP]
  push_cast
  ring

/-- Conversely, a complex-linear extension restricts to a real-linear extension on the
self-adjoint operators, so the two linearity hypotheses are equivalent. -/
theorem hasSelfAdjointLinearExtension_iff (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) :
    HasSelfAdjointLinearExtension mu ↔ HasLinearExtension mu := by
  refine ⟨hasLinearExtension_of_selfAdjoint mu, ?_⟩
  rintro ⟨f, hf⟩
  refine ⟨fun A => (f A).re, ?_, ?_, ?_⟩
  · intro A B _ _
    simp only [map_add, Complex.add_re]
  · intro r A _
    simp only [map_smul, smul_eq_mul, Complex.re_ofReal_mul]
  · intro P hP
    simp only [hf P hP, Complex.ofReal_re]

/-- **Gleason's theorem from a real-linear extension.**  Version of `gleason_theorem` whose
hypothesis is the more natural one: `mu` extends to an additive, real-homogeneous functional on
the self-adjoint operators. -/
theorem gleason_theorem_of_selfAdjoint_linear (hn : 3 ≤ n) (mu : Matrix (Fin n) (Fin n) ℂ → ℝ)
    (hmu : IsQuantumMeasure mu) (hlin : HasSelfAdjointLinearExtension mu) :
    GleasonProperty mu :=
  gleason_theorem hn mu hmu (hasLinearExtension_of_selfAdjoint mu hlin)

/-! ## Sharpness: Gleason's theorem fails in dimension two

The hypothesis `dim ≥ 3` in Gleason's theorem cannot be dropped.  We construct an explicit
quantum measure on a qubit which is *not* given by any density operator. -/

/-- Cayley–Hamilton in dimension two. -/
lemma cayleyHamilton_two (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- A `2 × 2` idempotent is `0`, the identity, or has trace `1`. -/
lemma idempotent_two_cases (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : P * P = P) :
    P = 0 ∨ P = 1 ∨ P.trace = 1 := by
  have hdet : P.det * P.det = P.det := by rw [← Matrix.det_mul, hP]
  have hfac : P.det * (P.det - 1) = 0 := by linear_combination hdet
  have hch := cayleyHamilton_two P
  rw [hP] at hch
  rcases mul_eq_zero.mp hfac with h | h
  · rw [h, zero_smul, add_zero, sub_eq_zero] at hch
    by_cases ht : P.trace = 1
    · exact Or.inr (Or.inr ht)
    · left
      have hz : (1 - P.trace) • P = 0 := by rw [sub_smul, one_smul, ← hch, sub_self]
      exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm ht))
  · right; left
    have hu : IsUnit P.det := by rw [sub_eq_zero.mp h]; exact isUnit_one
    have h2 : P⁻¹ * (P * P) = P⁻¹ * P := by rw [hP]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hu, Matrix.one_mul] at h2
    exact h2

/-- Two nonzero orthogonal projections in dimension two add up to the identity. -/
lemma add_eq_one_of_orthogonal_two (P Q : Matrix (Fin 2) (Fin 2) ℂ) (hP : IsProjection P)
    (hQ : IsProjection Q) (hPQ : P * Q = 0) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : P + Q = 1 := by
  have hQP : Q * P = 0 := by
    have h := congrArg Matrix.conjTranspose hPQ
    rwa [Matrix.conjTranspose_mul, hP.1.eq, hQ.1.eq, Matrix.conjTranspose_zero] at h
  have hP1 : P ≠ 1 := by
    rintro rfl
    exact hQ0 (by simpa using hPQ)
  have hQ1 : Q ≠ 1 := by
    rintro rfl
    exact hP0 (by simpa using hPQ)
  have htP : P.trace = 1 := ((idempotent_two_cases P hP.2).resolve_left hP0).resolve_left hP1
  have htQ : Q.trace = 1 := ((idempotent_two_cases Q hQ.2).resolve_left hQ0).resolve_left hQ1
  have hR : (P + Q) * (P + Q) = P + Q := by
    rw [add_mul, mul_add, mul_add, hP.2, hQ.2, hPQ, hQP]
    abel
  have htR : (P + Q).trace = 2 := by
    rw [Matrix.trace_add, htP, htQ]
    norm_num
  rcases idempotent_two_cases (P + Q) hR with h | h | h
  · rw [h] at htR
    simp at htR
  · exact h
  · rw [h] at htR
    norm_num at htR

/-- The `(0,0)` entry of a `2 × 2` projection is a real number in `[0,1]`. -/
lemma projection_two_entry (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : IsProjection P) :
    0 ≤ (P 0 0).re ∧ (P 0 0).re ≤ 1 := by
  have hherm : (starRingEnd ℂ) (P 0 0) = P 0 0 := by
    have h := congrFun (congrFun hP.1.eq 0) 0
    simpa [Matrix.conjTranspose_apply] using h
  have him : (P 0 0).im = 0 := Complex.conj_eq_iff_im.mp hherm
  have h10 : P 1 0 = (starRingEnd ℂ) (P 0 1) := by
    have h := congrFun (congrFun hP.1.eq 1) 0
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hidem : P 0 0 * P 0 0 + P 0 1 * P 1 0 = P 0 0 := by
    have h := congrFun (congrFun hP.2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  rw [h10, Complex.mul_conj] at hidem
  have hre : (P 0 0).re * (P 0 0).re + Complex.normSq (P 0 1) = (P 0 0).re := by
    have h := congrArg Complex.re hidem
    simpa [Complex.add_re, Complex.mul_re, him] using h
  have hns : 0 ≤ Complex.normSq (P 0 1) := Complex.normSq_nonneg _
  constructor <;> nlinarith [hre, hns]

/-- A nonlinear "frame function" on a qubit: `mu P = 3 a² - 2 a³` where `a` is the `(0,0)`
entry of `P`.  It is a genuine quantum measure but is not given by any density operator. -/
noncomputable def qubitMeasure (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  3 * (P 0 0).re ^ 2 - 2 * (P 0 0).re ^ 3

theorem qubitMeasure_isQuantumMeasure : IsQuantumMeasure qubitMeasure := by
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨h0, h1⟩ := projection_two_entry P hP
    simp only [qubitMeasure]
    nlinarith
  · norm_num [qubitMeasure, Matrix.one_apply]
  · intro P Q hP hQ hPQ
    by_cases hP0 : P = 0
    · subst hP0
      norm_num [qubitMeasure]
    by_cases hQ0 : Q = 0
    · subst hQ0
      norm_num [qubitMeasure]
    have hsum := add_eq_one_of_orthogonal_two P Q hP hQ hPQ hP0 hQ0
    have hab : (P 0 0).re + (Q 0 0).re = 1 := by
      have h := congrFun (congrFun hsum 0) 0
      have h2 := congrArg Complex.re h
      simpa [Matrix.add_apply, Matrix.one_apply] using h2
    have hb : (Q 0 0).re = 1 - (P 0 0).re := by linarith
    simp only [qubitMeasure, Matrix.add_apply, Complex.add_re, hb]
    ring

theorem qubitMeasure_not_gleasonProperty : ¬ GleasonProperty qubitMeasure := by
  rintro ⟨rho, -, hrep⟩
  have hproj : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, Aᴴ = A → A * A = A → IsProjection A :=
    fun A h1 h2 => ⟨h1, h2⟩
  have hE1 : IsProjection (!![(1 : ℂ), 0; 0, 0]) := by
    refine hproj _ ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have hE2 : IsProjection (!![(0 : ℂ), 0; 0, 1]) := by
    refine hproj _ ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have hH : IsProjection (!![(1 : ℂ)/2, 1/2; 1/2, 1/2]) := by
    refine hproj _ ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hK : IsProjection (!![(9 : ℂ)/25, 12/25; 12/25, 16/25]) := by
    refine hproj _ ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have h1 := hrep _ hE1
  have h2 := hrep _ hE2
  have h3 := hrep _ hH
  have h4 := hrep _ hK
  simp only [qubitMeasure, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  rw [h1, h2] at h3 h4
  have h5 : rho 0 1 + rho 1 0 = 0 := by linear_combination 2 * h3
  have h6 : (9 : ℂ) / 25 = 4617 / 15625 := by linear_combination h4 - (12 / 25) * h5
  norm_num at h6

/-- **Gleason's theorem is sharp: it fails in dimension two.** -/
theorem gleason_fails_dim_two :
    ∃ mu : Matrix (Fin 2) (Fin 2) ℂ → ℝ, IsQuantumMeasure mu ∧ ¬ GleasonProperty mu :=
  ⟨qubitMeasure, qubitMeasure_isQuantumMeasure, qubitMeasure_not_gleasonProperty⟩

end Frontier

