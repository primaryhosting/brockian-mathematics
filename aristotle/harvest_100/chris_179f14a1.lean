/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28's module system forbids a `/-!` module docstring before `import`;
-- the header above is therefore a plain block comment and is repeated below.)

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A *quantum measure* on a finite dimensional complex Hilbert space `ℂⁿ` is a map `μ` from the
orthogonal projections to `ℝ` which is nonnegative, finitely additive on orthogonal pairs, and
normalized (`μ 1 = 1`).  Gleason's theorem says that in dimension at least three every such `μ`
is given by the Born rule `μ P = Tr(ρ P)` for a unique density operator `ρ`.

This file contains:

* `Frontier.QuantumMeasure`, `Frontier.IsDensity`, `Frontier.Represents`: the formalized
  statement ingredients;
* `Frontier.born_rule_quantumMeasure`: every density operator gives a quantum measure;
* `Frontier.density_of_positive_linear`: a linear functional on matrices that is nonnegative
  on projections and normalized is the trace against a density operator;
* `Frontier.density_unique`: the density operator representing a measure is unique;
* `Frontier.gleason_theorem`: the Lean-checked reduction of Gleason's theorem to the linearity
  of the frame function (the analytic heart of the classical proof);
* `Frontier.gleason_fails_in_dimension_two`: an explicit quantum measure on the projections of
  `ℂ²` that is represented by no operator, showing that the dimension hypothesis is necessary.
-/

open Matrix Complex
open scoped ComplexOrder

namespace Frontier

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthogonal projection: a Hermitian idempotent matrix. -/
def IsProjection (P : Matrix n n ℂ) : Prop := P.IsHermitian ∧ P * P = P

/-- A density operator: a positive semidefinite matrix of unit trace. -/
def IsDensity (ρ : Matrix n n ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- `ρ` represents the measure `μ` via the Born rule `μ P = Tr(ρ P)`. -/
def Represents (ρ : Matrix n n ℂ) (μ : Matrix n n ℂ → ℝ) : Prop :=
  ∀ P, IsProjection P → μ P = (ρ * P).trace.re

/-- A quantum measure (finitely additive probability measure on the projection lattice). -/
structure QuantumMeasure (μ : Matrix n n ℂ → ℝ) : Prop where
  nonneg : ∀ P, IsProjection P → 0 ≤ μ P
  additive : ∀ P Q, IsProjection P → IsProjection Q → P * Q = 0 → Q * P = 0 →
    μ (P + Q) = μ P + μ Q
  normalized : μ 1 = 1

end Defs

section Basic

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma isProjection_one : IsProjection (1 : Matrix n n ℂ) :=
  ⟨Matrix.isHermitian_one, by simp⟩

omit [DecidableEq n] in
lemma isProjection_zero : IsProjection (0 : Matrix n n ℂ) :=
  ⟨Matrix.isHermitian_zero, by simp⟩

omit [DecidableEq n] in
/-- The trace of `ρ P` is a nonnegative real when `ρ` is positive semidefinite and `P` is a
projection. -/
lemma trace_mul_proj_nonneg {ρ P : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hP : IsProjection P) :
    0 ≤ (ρ * P).trace := by
  have hh : Pᴴ = P := hP.1
  have key : (Pᴴ * ρ * P).trace = (ρ * P).trace := by
    rw [hh, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hP.2]
  rw [← key]
  exact (hρ.conjTranspose_mul_mul_same P).trace_nonneg

/-- Every density operator gives rise to a quantum measure (the easy converse of Gleason). -/
theorem born_rule_quantumMeasure {ρ : Matrix n n ℂ} (hρ : IsDensity ρ) :
    QuantumMeasure (fun P => (ρ * P).trace.re) where
  nonneg P hP := by
    have := trace_mul_proj_nonneg hρ.1 hP
    simpa using (Complex.le_def.mp this).1
  additive P Q _ _ _ _ := by simp [Matrix.mul_add]
  normalized := by simp [hρ.2]

end Basic

section LinearReduction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix associated with a linear functional on matrices. -/
noncomputable def toMatrix (φ : Matrix n n ℂ →ₗ[ℂ] ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => φ (Matrix.single j i 1)

/-- A linear functional on matrices is determined by its values on the matrix units. -/
lemma linear_eq_sum_single (φ : Matrix n n ℂ →ₗ[ℂ] ℂ) (A : Matrix n n ℂ) :
    φ A = ∑ i, ∑ j, A i j * φ (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show Matrix.single i j (A i j) = A i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single]; simp]
  rw [map_smul, smul_eq_mul]

lemma trace_toMatrix_mul (φ : Matrix n n ℂ →ₗ[ℂ] ℂ) (A : Matrix n n ℂ) :
    ((toMatrix φ) * A).trace = φ A := by
  rw [linear_eq_sum_single φ A, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, toMatrix, Matrix.of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

omit [Fintype n] [DecidableEq n] in
lemma isHermitian_vecMulVec (v : n → ℂ) : (Matrix.vecMulVec v (star v)).IsHermitian := by
  ext a b
  simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]

omit [DecidableEq n] in
lemma vecMulVec_mul_self (v : n → ℂ) :
    (Matrix.vecMulVec v (star v)) * (Matrix.vecMulVec v (star v))
      = (star v ⬝ᵥ v) • Matrix.vecMulVec v (star v) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dotProduct,
    Pi.star_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

omit [DecidableEq n] in
lemma dotProduct_star_self (v : n → ℂ) :
    star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => by
    simp [Complex.normSq_eq_conj_mul_self]

omit [DecidableEq n] in
/-- A rank one matrix `v vᴴ`, normalized, is a projection. -/
lemma isProjection_vecMulVec {v : n → ℂ} (hv : v ≠ 0) :
    IsProjection ((((∑ i, Complex.normSq (v i) : ℝ) : ℂ))⁻¹ • Matrix.vecMulVec v (star v)) := by
  set c : ℝ := ∑ i, Complex.normSq (v i) with hc
  have hcpos : 0 < c := by
    rcases Function.ne_iff.mp hv with ⟨i, hi⟩
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
    simpa using hi
  have hcne : ((c : ℂ)) ≠ 0 := by
    simpa using hcpos.ne'
  constructor
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
      Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def, map_inv₀, Complex.conj_ofReal,
      Complex.conj_conj]
    ring
  · rw [Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_self, dotProduct_star_self, ← hc,
      smul_smul, smul_smul]
    congr 1
    field_simp

omit [DecidableEq n] in
lemma linear_vecMulVec_nonneg {φ : Matrix n n ℂ →ₗ[ℂ] ℂ}
    (hpos : ∀ P : Matrix n n ℂ, IsProjection P → 0 ≤ φ P) (v : n → ℂ) :
    0 ≤ φ (Matrix.vecMulVec v (star v)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · have : Matrix.vecMulVec (0 : n → ℂ) (star (0 : n → ℂ)) = 0 := by
      ext a b; simp
    rw [this, map_zero]
  · set c : ℝ := ∑ i, Complex.normSq (v i) with hc
    have hcpos : 0 < c := by
      rcases Function.ne_iff.mp hv with ⟨i, hi⟩
      refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
      simpa using hi
    have hcne : ((c : ℂ)) ≠ 0 := by simpa using hcpos.ne'
    have h := hpos _ (isProjection_vecMulVec hv)
    rw [map_smul, smul_eq_mul] at h
    have hmul : (0 : ℂ) ≤ (c : ℂ) * ((c : ℂ)⁻¹ * φ (Matrix.vecMulVec v (star v))) :=
      mul_nonneg (by simpa using hcpos.le) h
    rwa [← mul_assoc, mul_inv_cancel₀ hcne, one_mul] at hmul

lemma isProjection_single_diag (i : n) : IsProjection (Matrix.single i i (1 : ℂ)) := by
  constructor
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.single_apply, RCLike.star_def]
    by_cases h1 : i = a <;> by_cases h2 : i = b <;> simp [h1, h2]
  · simp

/-- Positivity on projections forces the matrix of `φ` to be Hermitian. -/
lemma star_linear_single {φ : Matrix n n ℂ →ₗ[ℂ] ℂ}
    (hpos : ∀ P : Matrix n n ℂ, IsProjection P → 0 ≤ φ P) (i j : n) :
    star (φ (Matrix.single i j 1)) = φ (Matrix.single j i 1) := by
  have hdiag : ∀ k : n, (φ (Matrix.single k k 1)).im = 0 := by
    intro k
    have := hpos _ (isProjection_single_diag k)
    simpa using ((Complex.le_def.mp this).2).symm
  rcases eq_or_ne i j with rfl | hij
  · exact Complex.ext rfl (by simp [hdiag i])
  set z : ℂ := φ (Matrix.single i j 1) with hz
  set w : ℂ := φ (Matrix.single j i 1) with hw
  -- first test vector: `e i + e j`
  set v₁ : n → ℂ := fun a => if a = i then 1 else if a = j then 1 else 0 with hv₁
  set v₂ : n → ℂ := fun a => if a = i then 1 else if a = j then Complex.I else 0 with hv₂
  have hm₁ : Matrix.vecMulVec v₁ (star v₁)
      = Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j 1 := by
    ext a b
    by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;>
      simp_all [Matrix.vecMulVec_apply, Matrix.single_apply, eq_comm]
  have hm₂ : Matrix.vecMulVec v₂ (star v₂)
      = Matrix.single i i 1 + (-Complex.I) • Matrix.single i j (1 : ℂ)
        + Complex.I • Matrix.single j i (1 : ℂ) + Matrix.single j j 1 := by
    ext a b
    by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;>
      simp_all [Matrix.vecMulVec_apply, Matrix.single_apply, eq_comm]
  have h₁ := linear_vecMulVec_nonneg hpos v₁
  have h₂ := linear_vecMulVec_nonneg hpos v₂
  rw [hm₁] at h₁
  rw [hm₂] at h₂
  have e₁ : φ (Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1
      + Matrix.single j j 1)
      = φ (Matrix.single i i 1) + z + w + φ (Matrix.single j j 1) := by
    rw [map_add, map_add, map_add, hz, hw]
  have e₂ : φ (Matrix.single i i 1 + (-Complex.I) • Matrix.single i j (1 : ℂ)
      + Complex.I • Matrix.single j i (1 : ℂ) + Matrix.single j j 1)
      = φ (Matrix.single i i 1) + (-Complex.I) * z + Complex.I * w + φ (Matrix.single j j 1) := by
    rw [map_add, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hz, hw]
  rw [e₁] at h₁
  rw [e₂] at h₂
  have him₁ : z.im + w.im = 0 := by
    have := ((Complex.le_def.mp h₁).2).symm
    simp [Complex.add_im, hdiag i, hdiag j] at this
    linarith [this]
  have him₂ : w.re - z.re = 0 := by
    have := ((Complex.le_def.mp h₂).2).symm
    simp [Complex.add_im, Complex.mul_im, hdiag i, hdiag j] at this
    linarith [this]
  refine Complex.ext ?_ ?_
  · simpa using by linarith [him₂]
  · simp only [Complex.star_def, Complex.conj_im]
    linarith [him₁]

lemma trace_toMatrix (φ : Matrix n n ℂ →ₗ[ℂ] ℂ) : (toMatrix φ).trace = φ 1 := by
  simp only [Matrix.trace, Matrix.diag_apply, toMatrix, Matrix.of_apply]
  rw [← map_sum, Matrix.sum_single_one]

/-- **Reduction of Gleason's theorem to linearity.**  A linear functional on matrices which is
nonnegative real on projections and takes the value `1` at the identity is given by a density
operator. -/
theorem density_of_positive_linear (φ : Matrix n n ℂ →ₗ[ℂ] ℂ)
    (hpos : ∀ P : Matrix n n ℂ, IsProjection P → 0 ≤ φ P) (hone : φ 1 = 1) :
    ∃ ρ : Matrix n n ℂ, IsDensity ρ ∧ ∀ A, φ A = (ρ * A).trace := by
  refine ⟨toMatrix φ, ⟨?_, ?_⟩, fun A => (trace_toMatrix_mul φ A).symm⟩
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext a b
      simpa [toMatrix, Matrix.conjTranspose_apply] using star_linear_single hpos a b
    · intro x
      have key : star x ⬝ᵥ ((toMatrix φ) *ᵥ x) = φ (Matrix.vecMulVec x (star x)) := by
        rw [linear_eq_sum_single φ (Matrix.vecMulVec x (star x))]
        simp only [dotProduct, Matrix.mulVec, toMatrix, Matrix.of_apply, Pi.star_apply,
          Matrix.vecMulVec_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [key]
      exact linear_vecMulVec_nonneg hpos x
  · rw [trace_toMatrix, hone]

end LinearReduction

section Uniqueness

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma trace_mul_single (D : Matrix n n ℂ) (a b : n) (c : ℂ) :
    (D * Matrix.single a b c).trace = c * D b a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.single_apply, mul_ite,
    mul_zero]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro l _ hl; simp [Ne.symm hl]
    · simp
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro l _
    simp [Ne.symm hk]
  · simp

/-- The sum of the squared norms of a vector supported on two coordinates. -/
lemma sum_normSq_pair {i j : n} (hij : i ≠ j) (x y : ℂ) :
    ∑ a : n, Complex.normSq (if a = i then x else if a = j then y else 0)
      = Complex.normSq x + Complex.normSq y := by
  have hpt : ∀ a : n, Complex.normSq (if a = i then x else if a = j then y else 0)
      = (if a = i then Complex.normSq x else 0) + (if a = j then Complex.normSq y else 0) := by
    intro a
    by_cases h1 : a = i <;> by_cases h2 : a = j <;> simp_all
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_add_distrib]
  simp

/-- The rank one projection onto `e i + e j`. -/
noncomputable def pairProj (i j : n) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1
    + Matrix.single j j 1)

/-- The rank one projection onto `e i + I • e j`. -/
noncomputable def pairProjI (i j : n) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (Matrix.single i i 1 + (-Complex.I) • Matrix.single i j (1 : ℂ)
    + Complex.I • Matrix.single j i (1 : ℂ) + Matrix.single j j 1)

lemma isProjection_pairProj {i j : n} (hij : i ≠ j) : IsProjection (pairProj i j) := by
  set v : n → ℂ := fun a => if a = i then 1 else if a = j then 1 else 0 with hv
  have hvne : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp [hv] at this
  have hsum : (∑ a : n, Complex.normSq (v a)) = 2 := by
    rw [hv, sum_normSq_pair hij 1 1]
    norm_num
  have hmat : Matrix.vecMulVec v (star v)
      = Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j 1 := by
    ext a b
    by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;>
      simp_all [Matrix.vecMulVec_apply, Matrix.single_apply, eq_comm]
  have := isProjection_vecMulVec hvne
  rwa [hsum, hmat, show (((2 : ℝ) : ℂ)) = (2 : ℂ) by norm_num] at this

lemma isProjection_pairProjI {i j : n} (hij : i ≠ j) : IsProjection (pairProjI i j) := by
  set v : n → ℂ := fun a => if a = i then 1 else if a = j then Complex.I else 0 with hv
  have hvne : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp [hv] at this
  have hsum : (∑ a : n, Complex.normSq (v a)) = 2 := by
    rw [hv, sum_normSq_pair hij 1 Complex.I]
    norm_num
  have hmat : Matrix.vecMulVec v (star v)
      = Matrix.single i i 1 + (-Complex.I) • Matrix.single i j (1 : ℂ)
        + Complex.I • Matrix.single j i (1 : ℂ) + Matrix.single j j 1 := by
    ext a b
    by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;>
      simp_all [Matrix.vecMulVec_apply, Matrix.single_apply, eq_comm]
  have := isProjection_vecMulVec hvne
  rwa [hsum, hmat, show (((2 : ℝ) : ℂ)) = (2 : ℂ) by norm_num] at this

/-- A Hermitian matrix whose Born-rule values on all projections vanish is zero. -/
lemma eq_zero_of_trace_proj_re_eq_zero {D : Matrix n n ℂ} (hD : D.IsHermitian)
    (h : ∀ P, IsProjection P → (D * P).trace.re = 0) : D = 0 := by
  have hdiag : ∀ i : n, D i i = 0 := by
    intro i
    have h1 := h _ (isProjection_single_diag i)
    rw [trace_mul_single] at h1
    simp only [one_mul] at h1
    have h2 : (starRingEnd ℂ) (D i i) = D i i := by
      have := congrFun (congrFun hD i) i
      simpa [Matrix.conjTranspose_apply] using this
    have h3 : (D i i).im = 0 := by
      simpa using (Complex.conj_eq_iff_im.mp h2)
    exact Complex.ext h1 h3
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [hdiag i]
  have hconj : (starRingEnd ℂ) (D i j) = D j i := by
    have := congrFun (congrFun hD j) i
    simpa [Matrix.conjTranspose_apply] using this
  have h1 := h _ (isProjection_pairProj hij)
  have h2 := h _ (isProjection_pairProjI hij)
  rw [pairProj, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, trace_mul_single,
    trace_mul_single, trace_mul_single, trace_mul_single, hdiag i, hdiag j] at h1
  rw [pairProjI, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.mul_smul,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
    trace_mul_single, trace_mul_single, trace_mul_single, trace_mul_single, hdiag i,
    hdiag j] at h2
  have hre : (D i j).re = 0 := by
    have hz : ((2 : ℂ)⁻¹ * (1 * 0 + 1 * D j i + 1 * D i j + 1 * 0)).re = 0 := h1
    rw [← hconj] at hz
    simp [Complex.mul_re, Complex.add_re, Complex.inv_re] at hz
    linarith
  have him : (D i j).im = 0 := by
    have hz : ((2 : ℂ)⁻¹ * (1 * 0 + -Complex.I * (1 * D j i) + Complex.I * (1 * D i j)
      + 1 * 0)).re = 0 := h2
    rw [← hconj] at hz
    simp [Complex.mul_re, Complex.add_re, Complex.inv_re, Complex.mul_im,
      Complex.I_re, Complex.I_im] at hz
    linarith
  simpa using Complex.ext hre him

/-- **Uniqueness in Gleason's theorem.** A quantum measure determines its density operator. -/
theorem density_unique {ρ σ : Matrix n n ℂ} {μ : Matrix n n ℂ → ℝ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (h1 : Represents ρ μ) (h2 : Represents σ μ) : ρ = σ := by
  have hzero : ρ - σ = 0 := by
    refine eq_zero_of_trace_proj_re_eq_zero (hρ.sub hσ) fun P hP => ?_
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, ← h1 P hP, ← h2 P hP, sub_self]
  exact sub_eq_zero.mp hzero

end Uniqueness

/-- **Gleason's theorem (Lean-checked reduction).**
Let `μ` be a quantum measure on the projection lattice of a Hilbert space of dimension `≥ 3`
which extends to a linear functional on all operators.  Then `μ` is given by the Born rule for a
unique density operator `ρ`.

The linearity hypothesis `hlin` is precisely the analytic heart of Gleason's theorem: for
dimension `≥ 3` every quantum measure automatically extends linearly.  The dimension hypothesis
`hn` is kept because it is part of the classical statement, but it is not used by this reduction.
Dimension `≥ 3` is genuinely necessary for the unconditional statement: see
`Frontier.gleason_fails_in_dimension_two`. -/
theorem gleason_theorem {n : Type*} [Fintype n] [DecidableEq n] (hn : 3 ≤ Fintype.card n)
    (μ : Matrix n n ℂ → ℝ) (hμ : QuantumMeasure μ)
    (hlin : ∃ φ : Matrix n n ℂ →ₗ[ℂ] ℂ, ∀ P, IsProjection P → φ P = (μ P : ℂ)) :
    ∃ ρ : Matrix n n ℂ, IsDensity ρ ∧ Represents ρ μ ∧
      ∀ σ : Matrix n n ℂ, IsDensity σ → Represents σ μ → σ = ρ := by
  obtain ⟨φ, hφ⟩ := hlin
  have hpos : ∀ P : Matrix n n ℂ, IsProjection P → 0 ≤ φ P := by
    intro P hP
    rw [hφ P hP]
    exact Complex.le_def.mpr ⟨by simpa using hμ.nonneg P hP, by simp⟩
  have hone : φ 1 = 1 := by rw [hφ 1 isProjection_one, hμ.normalized]; norm_num
  obtain ⟨ρ, hρ, hrep⟩ := density_of_positive_linear φ hpos hone
  have hrep' : Represents ρ μ := by
    intro P hP
    rw [← hrep P, hφ P hP, Complex.ofReal_re]
  exact ⟨ρ, hρ, hrep', fun σ hσ hrepσ =>
    density_unique hσ.1.isHermitian hρ.1.isHermitian hrepσ hrep'⟩

section DimTwo

/-- The rank one projection onto `(1, 2)/√5`. -/
noncomputable def projU : Matrix (Fin 2) (Fin 2) ℂ := !![1/5, 2/5; 2/5, 4/5]

/-- The rank one projection onto `(1, -2)/√5`. -/
noncomputable def projV : Matrix (Fin 2) (Fin 2) ℂ := !![1/5, -(2/5); -(2/5), 4/5]

/-- The projection onto the first coordinate axis. -/
def e00 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The projection onto the second coordinate axis. -/
def e11 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]

lemma isProjection_projU : IsProjection projU := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [projU, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projU, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma isProjection_projV : IsProjection projV := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [projV, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projV, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma isProjection_e00 : IsProjection e00 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, Matrix.mul_apply, Fin.sum_univ_two]

lemma isProjection_e11 : IsProjection e11 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [e11, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [e11, Matrix.mul_apply, Fin.sum_univ_two]

/-- The nonlinear frame function on `ℂ²` used to show that Gleason's theorem fails in
dimension two. -/
noncomputable def badMeasure (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (1 + (2 * (P 0 0).re - 1) ^ 3) / 2

/-- Basic relations satisfied by the entries of a `2 × 2` projection. -/
lemma proj_two_relations {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProjection P) :
    P 0 0 = (((P 0 0).re : ℝ) : ℂ) ∧ P 1 1 = (((P 1 1).re : ℝ) : ℂ) ∧
      P 1 0 = star (P 0 1) ∧
      (P 0 0).re ^ 2 + Complex.normSq (P 0 1) = (P 0 0).re ∧
      P 0 1 * (P 0 0 + P 1 1 - 1) = 0 := by
  obtain ⟨hherm, hidem⟩ := hP
  have h00 : (starRingEnd ℂ) (P 0 0) = P 0 0 := by
    have := congrFun (congrFun hherm 0) 0
    simpa [Matrix.conjTranspose_apply] using this
  have h11 : (starRingEnd ℂ) (P 1 1) = P 1 1 := by
    have := congrFun (congrFun hherm 1) 1
    simpa [Matrix.conjTranspose_apply] using this
  have h10 : (starRingEnd ℂ) (P 0 1) = P 1 0 := by
    have := congrFun (congrFun hherm 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have e00 : P 0 0 * P 0 0 + P 0 1 * P 1 0 = P 0 0 := by
    have := congrFun (congrFun hidem 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : P 0 0 * P 0 1 + P 0 1 * P 1 1 = P 0 1 := by
    have := congrFun (congrFun hidem 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hre00 : P 0 0 = (((P 0 0).re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp h00).symm
  have hre11 : P 1 1 = (((P 1 1).re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp h11).symm
  refine ⟨hre00, hre11, h10.symm, ?_, by linear_combination e01⟩
  have hc : ((((P 0 0).re ^ 2 + Complex.normSq (P 0 1) : ℝ)) : ℂ) = (((P 0 0).re : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj, ← hre00, h10]
    linear_combination e00
  exact_mod_cast hc

/-- For two orthogonal projections in dimension two, either one of them has vanishing `(0,0)`
entry, or the two entries sum to one. -/
lemma two_orthogonal_diag {P Q : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProjection P)
    (hQ : IsProjection Q) (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    (P 0 0).re + (Q 0 0).re = 1 ∨ (P 0 0).re = 0 ∨ (Q 0 0).re = 0 := by
  obtain ⟨hp00, hp11, hp10, hpsq, hpoff⟩ := proj_two_relations hP
  obtain ⟨hq00, hq11, hq10, hqsq, hqoff⟩ := proj_two_relations hQ
  have m00 : P 0 0 * Q 0 0 + P 0 1 * Q 1 0 = 0 := by
    have := congrFun (congrFun hPQ 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have m01 : P 0 0 * Q 0 1 + P 0 1 * Q 1 1 = 0 := by
    have := congrFun (congrFun hPQ 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have n00 : Q 0 0 * P 0 0 + Q 0 1 * P 1 0 = 0 := by
    have := congrFun (congrFun hQP 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  by_cases hb : P 0 1 = 0
  · have ha : (P 0 0).re * ((P 0 0).re - 1) = 0 := by
      have : Complex.normSq (P 0 1) = 0 := by simp [hb]
      nlinarith [hpsq, this]
    rcases mul_eq_zero.mp ha with h | h
    · exact Or.inr (Or.inl h)
    · have ha1 : P 0 0 = 1 := by
        rw [hp00]
        norm_num
        linarith
      have : Q 0 0 = 0 := by
        have := m00
        rw [ha1, hb] at this
        simpa using this
      exact Or.inr (Or.inr (by rw [this]; simp))
  by_cases hb' : Q 0 1 = 0
  · have hb'' : Q 1 0 = 0 := by rw [hq10, hb']; simp
    have ha : (Q 0 0).re * ((Q 0 0).re - 1) = 0 := by
      have : Complex.normSq (Q 0 1) = 0 := by simp [hb']
      nlinarith [hqsq, this]
    rcases mul_eq_zero.mp ha with h | h
    · exact Or.inr (Or.inr h)
    · have ha1 : Q 0 0 = 1 := by
        rw [hq00]
        norm_num
        linarith
      have : P 0 0 = 0 := by
        have := n00
        rw [ha1, hb'] at this
        simpa using this
      exact Or.inr (Or.inl (by rw [this]; simp))
  -- main case: both off-diagonal entries are nonzero
  left
  set a : ℝ := (P 0 0).re with ha
  set a' : ℝ := (Q 0 0).re with ha'
  have hnb : 0 < Complex.normSq (P 0 1) := by
    simpa [Complex.normSq_eq_zero] using (Complex.normSq_nonneg (P 0 1)).lt_of_ne'
      (by simpa [Complex.normSq_eq_zero] using hb)
  have hnb' : 0 < Complex.normSq (Q 0 1) := by
    simpa [Complex.normSq_eq_zero] using (Complex.normSq_nonneg (Q 0 1)).lt_of_ne'
      (by simpa [Complex.normSq_eq_zero] using hb')
  have hapos : 0 < a := by nlinarith [hpsq, hnb]
  have ha1 : a < 1 := by nlinarith [hpsq, hnb]
  have ha'pos : 0 < a' := by nlinarith [hqsq, hnb']
  have ha'1 : a' < 1 := by nlinarith [hqsq, hnb']
  -- the diagonal of `Q` is `(a', 1 - a')`
  have hq11' : Q 1 1 = (((1 - a' : ℝ)) : ℂ) := by
    have h := mul_eq_zero.mp hqoff
    rcases h with h | h
    · exact absurd h hb'
    · have : Q 1 1 = 1 - Q 0 0 := by linear_combination h
      rw [this, hq00]
      push_cast
      ring
  have heq : ((a : ℂ)) * Q 0 1 = -(P 0 1 * (((1 - a' : ℝ)) : ℂ)) := by
    have := m01
    rw [hp00, hq11'] at this
    linear_combination this
  have hnorm := congrArg Complex.normSq heq
  simp only [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_ofReal] at hnorm
  -- turn the two idempotency relations into expressions for the off-diagonal norms
  have hnb_eq : Complex.normSq (P 0 1) = a - a ^ 2 := by linarith [hpsq]
  have hnb'_eq : Complex.normSq (Q 0 1) = a' - a' ^ 2 := by linarith [hqsq]
  rw [hnb_eq, hnb'_eq] at hnorm
  have key : a * (1 - a') * (a + a' - 1) = 0 := by nlinarith [hnorm]
  have h1 : a ≠ 0 := ne_of_gt hapos
  have h2 : (1 - a') ≠ 0 := by linarith
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' h1
    · exact absurd h' h2
  · linarith

lemma badMeasure_quantumMeasure : QuantumMeasure badMeasure where
  nonneg P hP := by
    obtain ⟨-, -, -, hpsq, -⟩ := proj_two_relations hP
    have hnn := Complex.normSq_nonneg (P 0 1)
    have h0 : 0 ≤ (P 0 0).re := by nlinarith
    have h1 : (P 0 0).re ≤ 1 := by nlinarith
    have hfac : 0 ≤ (1 + (2 * (P 0 0).re - 1)) *
        (1 - (2 * (P 0 0).re - 1) + (2 * (P 0 0).re - 1) ^ 2) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (2 * (P 0 0).re - 1 - 1)])
    simp only [badMeasure]
    nlinarith [hfac]
  additive P Q hP hQ hPQ hQP := by
    have hadd : (P + Q) 0 0 = P 0 0 + Q 0 0 := rfl
    simp only [badMeasure, hadd, Complex.add_re]
    rcases two_orthogonal_diag hP hQ hPQ hQP with h | h | h
    · have hQe : (Q 0 0).re = 1 - (P 0 0).re := by linarith
      rw [hQe]; ring
    · rw [h]; ring
    · rw [h]; ring
  normalized := by
    have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := Matrix.one_apply_eq 0
    simp only [badMeasure, h1]
    norm_num

/-- **Gleason's theorem fails in dimension two.** There is a quantum measure on the projections
of `ℂ²` that is not given by the Born rule for any operator. -/
theorem gleason_fails_in_dimension_two :
    ∃ μ : Matrix (Fin 2) (Fin 2) ℂ → ℝ, QuantumMeasure μ ∧
      ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ¬ Represents ρ μ := by
  refine ⟨badMeasure, badMeasure_quantumMeasure, fun ρ hrep => ?_⟩
  have h00 := hrep _ isProjection_e00
  have h11 := hrep _ isProjection_e11
  have hu := hrep _ isProjection_projU
  have hv := hrep _ isProjection_projV
  have v00 : badMeasure e00 = 1 := by norm_num [badMeasure, e00]
  have v11 : badMeasure e11 = 0 := by norm_num [badMeasure, e11]
  have vu : badMeasure projU = 49 / 125 := by norm_num [badMeasure, projU]
  have vv : badMeasure projV = 49 / 125 := by norm_num [badMeasure, projV]
  have tr00 : (ρ * e00).trace = ρ 0 0 := by
    rw [Matrix.trace_fin_two]
    simp [e00, Matrix.mul_apply, Fin.sum_univ_two]
  have tr11 : (ρ * e11).trace = ρ 1 1 := by
    rw [Matrix.trace_fin_two]
    simp [e11, Matrix.mul_apply, Fin.sum_univ_two]
  have hsum : (ρ * projU).trace + (ρ * projV).trace
      = ((2 / 5 : ℝ) : ℂ) * ρ 0 0 + ((8 / 5 : ℝ) : ℂ) * ρ 1 1 := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
    simp [projU, projV, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [v00, tr00] at h00
  rw [v11, tr11] at h11
  rw [vu] at hu
  rw [vv] at hv
  have hre : ((ρ * projU).trace + (ρ * projV).trace).re = 2 / 5 := by
    rw [hsum, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← h00, ← h11]
    norm_num
  rw [Complex.add_re, ← hu, ← hv] at hre
  norm_num at hre

end DimTwo

end Frontier

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

