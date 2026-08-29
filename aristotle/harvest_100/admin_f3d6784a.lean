import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions -/

/-- The rank-one (orthogonal) projection onto the line spanned by a unit vector `v`,
written as the matrix `v vᴴ`. -/
def rankOneProj (v : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.vecMulVec v (star v)

/-- A vector of `ℂⁿ` has unit length. -/
def IsUnitVec (v : Fin n → ℂ) : Prop := star v ⬝ᵥ v = 1

/-- An orthogonal projection: a self-adjoint idempotent matrix.  These are exactly the
matrices of orthogonal projections onto closed subspaces, i.e. the quantum events. -/
def IsProj (P : Matrix (Fin n) (Fin n) ℂ) : Prop := P.IsHermitian ∧ P * P = P

/-- A *quantum measure* (a.k.a. a probability measure on the lattice of quantum events):
a nonnegative, finitely additive, normalized function on orthogonal projections.
In finite dimension countable additivity is the same as finite additivity. -/
structure IsQuantumMeasure (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) : Prop where
  nonneg : ∀ P, IsProj P → 0 ≤ mu P
  additive : ∀ P Q, IsProj P → IsProj Q → P * Q = 0 → mu (P + Q) = mu P + mu Q
  normalized : mu 1 = 1

/-- A density operator: a positive semidefinite matrix of trace one. -/
def IsDensityOperator (rho : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  rho.PosSemidef ∧ rho.trace = 1

/-- **Gleason's analytic core in dimension `n`.**  This says that the restriction of any
quantum measure to the *rank-one* projections is given by a quadratic form, i.e. by a
Hermitian matrix.  This is the hard, dimension-dependent part of Gleason's theorem
(it is true exactly when `n ≠ 2`; for `n ≥ 3` it is Gleason's theorem, for `n = 2` it fails). -/
def FrameRepresentation (n : ℕ) : Prop :=
  ∀ mu : Matrix (Fin n) (Fin n) ℂ → ℝ, IsQuantumMeasure mu →
    ∃ rho : Matrix (Fin n) (Fin n) ℂ, rho.IsHermitian ∧
      ∀ v : Fin n → ℂ, IsUnitVec v →
        ((mu (rankOneProj v) : ℝ) : ℂ) = (rho * rankOneProj v).trace

/-! ## Rank-one projections -/

lemma rankOneProj_apply (v : Fin n → ℂ) (i j : Fin n) :
    rankOneProj v i j = v i * (starRingEnd ℂ) (v j) := rfl

lemma rankOneProj_mul (v w : Fin n → ℂ) :
    rankOneProj v * rankOneProj w = (star v ⬝ᵥ w) • Matrix.vecMulVec v (star w) := by
  ext i j
  simp only [rankOneProj, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
    dotProduct, Pi.star_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma isHermitian_rankOneProj (v : Fin n → ℂ) : (rankOneProj v).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, rankOneProj, Matrix.vecMulVec_apply, mul_comm]

lemma isProj_rankOneProj {v : Fin n → ℂ} (hv : IsUnitVec v) : IsProj (rankOneProj v) := by
  refine ⟨isHermitian_rankOneProj v, ?_⟩
  rw [rankOneProj_mul, hv, one_smul]
  rfl

lemma trace_mul_rankOneProj (rho : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (rho * rankOneProj v).trace = star v ⬝ᵥ (rho *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rankOneProj,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ## Finite additivity -/

lemma isProj_zero : IsProj (0 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨Matrix.isHermitian_zero, by simp⟩

lemma isProj_one : IsProj (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨Matrix.isHermitian_one, by simp⟩

lemma IsQuantumMeasure.map_zero {mu : Matrix (Fin n) (Fin n) ℂ → ℝ} (hmu : IsQuantumMeasure mu) :
    mu 0 = 0 := by
  have h := hmu.additive 0 0 isProj_zero isProj_zero (by simp)
  simp only [add_zero] at h
  linarith

lemma isProj_sum {s : Finset (Fin n)} {Q : Fin n → Matrix (Fin n) (Fin n) ℂ}
    (hQ : ∀ i ∈ s, IsProj (Q i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Q i * Q j = 0) :
    IsProj (∑ i ∈ s, Q i) := by
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun i hi => (hQ i hi).1
  · rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · exact (hQ i hi).2
    · intro j hj hji
      exact horth i hi j hj (Ne.symm hji)
    · intro h; exact absurd hi h

lemma IsQuantumMeasure.sum_eq {mu : Matrix (Fin n) (Fin n) ℂ → ℝ} (hmu : IsQuantumMeasure mu)
    {Q : Fin n → Matrix (Fin n) (Fin n) ℂ} {s : Finset (Fin n)}
    (hQ : ∀ i ∈ s, IsProj (Q i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Q i * Q j = 0) :
    mu (∑ i ∈ s, Q i) = ∑ i ∈ s, mu (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hmu.map_zero
  | insert a s ha ih =>
      have hQ' : ∀ i ∈ s, IsProj (Q i) := fun i hi => hQ i (Finset.mem_insert_of_mem hi)
      have horth' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Q i * Q j = 0 := fun i hi j hj hij =>
        horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hsum : IsProj (∑ i ∈ s, Q i) := isProj_sum hQ' horth'
      have hmul : Q a * (∑ i ∈ s, Q i) = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero fun j hj => ?_
        exact horth a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact ha hj)
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hmu.additive _ _ (hQ a (Finset.mem_insert_self a s)) hsum hmul, ih hQ' horth']

/-! ## Spectral decomposition into rank-one projections -/

lemma orthonormalBasis_dotProduct {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (i j : Fin n) :
    star (hA.eigenvectorBasis i).ofLp ⬝ᵥ (hA.eigenvectorBasis j).ofLp = if i = j then 1 else 0 := by
  have h := hA.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at h
  have hij := h i j
  rw [PiLp.inner_apply] at hij
  simp only [RCLike.inner_apply] at hij
  rw [dotProduct]
  simp only [Pi.star_apply]
  rw [← hij]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma isUnitVec_eigenvectorBasis {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (j : Fin n) :
    IsUnitVec (hA.eigenvectorBasis j).ofLp := by
  simpa using orthonormalBasis_dotProduct hA j j

lemma hermitian_eq_sum_rankOne {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    A = ∑ j, ((hA.eigenvalues j : ℝ) : ℂ) • rankOneProj (hA.eigenvectorBasis j).ofLp := by
  conv_lhs => rw [hA.spectral_theorem]
  ext i k
  simp only [rankOneProj, Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.star_apply, smul_eq_mul, Function.comp_apply,
    Matrix.IsHermitian.eigenvectorUnitary_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm ((hA.eigenvectorBasis x).ofLp i), mul_assoc]
  norm_cast

lemma proj_eigenvalues_eq_zero_or_one {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P) (j : Fin n) :
    hP.1.eigenvalues j = 0 ∨ hP.1.eigenvalues j = 1 := by
  have hb : IsUnitVec (hP.1.eigenvectorBasis j).ofLp := isUnitVec_eigenvectorBasis hP.1 j
  set b := (hP.1.eigenvectorBasis j).ofLp with hbdef
  set l := hP.1.eigenvalues j with hldef
  obtain ⟨i, hi⟩ : ∃ i, b i ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : star b ⬝ᵥ b = 0 := by simp [dotProduct, h]
    rw [hb] at h0
    exact one_ne_zero h0
  have h1 : P *ᵥ b = l • b := hP.1.mulVec_eigenvectorBasis j
  have h2 : P *ᵥ (P *ᵥ b) = P *ᵥ b := by rw [Matrix.mulVec_mulVec, hP.2]
  rw [h1, Matrix.mulVec_smul, h1, smul_smul] at h2
  have h3 := congrFun h2 i
  simp only [Pi.smul_apply, Complex.real_smul] at h3
  have h4 : ((l * l : ℝ) : ℂ) = ((l : ℝ) : ℂ) := mul_right_cancel₀ hi h3
  have h5 : l * l = l := by exact_mod_cast h4
  rcases mul_eq_zero.mp (show l * (l - 1) = 0 by nlinarith [h5]) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- Every orthogonal projection is a sum of pairwise orthogonal rank-one projections. -/
lemma proj_eq_sum_rankOne {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P) :
    ∃ (s : Finset (Fin n)) (b : Fin n → (Fin n → ℂ)),
      (∀ j, IsUnitVec (b j)) ∧
      (∀ i j, i ≠ j → rankOneProj (b i) * rankOneProj (b j) = 0) ∧
      P = ∑ j ∈ s, rankOneProj (b j) := by
  classical
  refine ⟨Finset.univ.filter (fun j => hP.1.eigenvalues j = 1),
    fun j => (hP.1.eigenvectorBasis j).ofLp, fun j => isUnitVec_eigenvectorBasis hP.1 j,
    fun i j hij => ?_, ?_⟩
  · rw [rankOneProj_mul, orthonormalBasis_dotProduct hP.1 i j, if_neg hij, zero_smul]
  · have hterm : ∀ j : Fin n,
        ((hP.1.eigenvalues j : ℝ) : ℂ) • rankOneProj (hP.1.eigenvectorBasis j).ofLp
          = if hP.1.eigenvalues j = 1 then rankOneProj (hP.1.eigenvectorBasis j).ofLp else 0 := by
      intro j
      rcases proj_eigenvalues_eq_zero_or_one hP j with h | h <;> rw [h] <;> simp
    rw [Finset.sum_filter]
    conv_lhs => rw [hermitian_eq_sum_rankOne hP.1]
    exact Finset.sum_congr rfl fun j _ => hterm j

/-! ## The reduction -/

/-- Given the quadratic-form representation on rank-one projections, the trace formula
holds for *all* projections. -/
theorem trace_formula_of_frame {mu : Matrix (Fin n) (Fin n) ℂ → ℝ} (hmu : IsQuantumMeasure mu)
    {rho : Matrix (Fin n) (Fin n) ℂ}
    (hframe : ∀ v : Fin n → ℂ, IsUnitVec v →
      ((mu (rankOneProj v) : ℝ) : ℂ) = (rho * rankOneProj v).trace)
    {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P) :
    ((mu P : ℝ) : ℂ) = (rho * P).trace := by
  obtain ⟨s, b, hb, horth, hPeq⟩ := proj_eq_sum_rankOne hP
  rw [hPeq, hmu.sum_eq (fun j _ => isProj_rankOneProj (hb j)) (fun i _ j _ hij => horth i j hij),
    Finset.mul_sum, Matrix.trace_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ => hframe (b j) (hb j)

/-- Rescaling a vector rescales the associated quadratic form. -/
lemma dotProduct_mulVec_smul (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    star (c • x) ⬝ᵥ (M *ᵥ (c • x)) = (star c * c) * (star x ⬝ᵥ (M *ᵥ x)) := by
  simp only [Matrix.mulVec_smul, star_smul, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotProduct_self_smul (c : ℂ) (x : Fin n → ℂ) :
    star (c • x) ⬝ᵥ (c • x) = (star c * c) * (star x ⬝ᵥ x) := by
  simp only [star_smul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem posSemidef_of_frame {mu : Matrix (Fin n) (Fin n) ℂ → ℝ} (hmu : IsQuantumMeasure mu)
    {rho : Matrix (Fin n) (Fin n) ℂ} (hrho : rho.IsHermitian)
    (hframe : ∀ v : Fin n → ℂ, IsUnitVec v →
      ((mu (rankOneProj v) : ℝ) : ℂ) = (rho * rankOneProj v).trace) :
    rho.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hrho fun x => ?_
  set r : ℝ := ∑ i, Complex.normSq (x i) with hrdef
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hxx : star x ⬝ᵥ x = (r : ℂ) := by
    rw [hrdef, dotProduct]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by
      simp [Complex.normSq_eq_conj_mul_self]
  by_cases hx : r = 0
  · have hx0 : x = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ Finset.univ) => Complex.normSq_nonneg (x i))).mp (hrdef ▸ hx) i
        (Finset.mem_univ i)
      exact Complex.normSq_eq_zero.mp this
    simp [hx0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hx)
    set t : ℝ := Real.sqrt r with htdef
    have htpos : 0 < t := Real.sqrt_pos.mpr hrpos
    have htt : t * t = r := Real.mul_self_sqrt hr0
    have ht2 : (t : ℂ) * (t : ℂ) = (r : ℂ) := by exact_mod_cast congrArg (fun s : ℝ => (s : ℂ)) htt
    set c : ℂ := ((t : ℂ))⁻¹ with hcdef
    have hcc : star c * c = ((r : ℂ))⁻¹ := by
      rw [hcdef, star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ht2]
    set v : Fin n → ℂ := c • x with hvdef
    have hv : IsUnitVec v := by
      rw [IsUnitVec, hvdef, dotProduct_self_smul, hcc, hxx, inv_mul_cancel₀]
      exact_mod_cast hrpos.ne'
    have hkey : star v ⬝ᵥ (rho *ᵥ v) = ((r : ℂ))⁻¹ * (star x ⬝ᵥ (rho *ᵥ x)) := by
      rw [hvdef, dotProduct_mulVec_smul, hcc]
    have hframe' := hframe v hv
    rw [trace_mul_rankOneProj] at hframe'
    have hfinal : star x ⬝ᵥ (rho *ᵥ x) = ((r * mu (rankOneProj v) : ℝ) : ℂ) := by
      have : (r : ℂ) * (star v ⬝ᵥ (rho *ᵥ v)) = star x ⬝ᵥ (rho *ᵥ x) := by
        rw [hkey, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hrpos.ne' : (r : ℂ) ≠ 0),
          one_mul]
      rw [← this, ← hframe']
      push_cast
      ring
    rw [hfinal]
    have : (0 : ℝ) ≤ r * mu (rankOneProj v) :=
      mul_nonneg hr0 (hmu.nonneg _ (isProj_rankOneProj hv))
    exact_mod_cast this

/-- The reduction of Gleason's theorem to its analytic core:  once the quantum measure is
known to be a quadratic form on rank-one projections, it is the trace against a genuine
density operator. -/
theorem gleason_of_frameRepresentation (hFrame : FrameRepresentation n)
    (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) (hmu : IsQuantumMeasure mu) :
    ∃ rho : Matrix (Fin n) (Fin n) ℂ, IsDensityOperator rho ∧
      ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProj P → ((mu P : ℝ) : ℂ) = (rho * P).trace := by
  obtain ⟨rho, hrho, hframe⟩ := hFrame mu hmu
  refine ⟨rho, ⟨posSemidef_of_frame hmu hrho hframe, ?_⟩, fun P hP =>
    trace_formula_of_frame hmu hframe hP⟩
  have h := trace_formula_of_frame hmu hframe (P := 1) isProj_one
  rw [mul_one, hmu.normalized] at h
  exact h.symm

/-- **Gleason's theorem** (reduction form).  On a complex Hilbert space of dimension `n ≥ 3`,
granted Gleason's analytic core `FrameRepresentation n`, every quantum measure is given by
a density operator: `mu P = tr (rho P)`.

The hypothesis `3 ≤ n` is the dimension hypothesis of Gleason's theorem; it is exactly what
is needed for `FrameRepresentation n` to hold, and is not used again in this reduction. -/
theorem gleason_theorem (n : ℕ) (hn : 3 ≤ n) (hFrame : FrameRepresentation n)
    (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) (hmu : IsQuantumMeasure mu) :
    ∃ rho : Matrix (Fin n) (Fin n) ℂ, IsDensityOperator rho ∧
      ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProj P → ((mu P : ℝ) : ℂ) = (rho * P).trace :=
  gleason_of_frameRepresentation hFrame mu hmu

/-! ## The converse: density operators give quantum measures -/

theorem isQuantumMeasure_of_density {rho : Matrix (Fin n) (Fin n) ℂ} (hrho : IsDensityOperator rho) :
    IsQuantumMeasure (fun P => (rho * P).trace.re) := by
  refine ⟨fun P hP => ?_, fun P Q _ _ _ => ?_, ?_⟩
  · have hconj : (Pᴴ * rho * P).trace = (rho * P).trace := by
      rw [hP.1, Matrix.trace_mul_comm (P * rho) P, ← Matrix.mul_assoc, hP.2,
        Matrix.trace_mul_comm]
    have hps : (Pᴴ * rho * P).PosSemidef := hrho.1.conjTranspose_mul_mul_same P
    have := hps.trace_nonneg
    rw [hconj] at this
    simpa using (Complex.le_def.mp this).1
  · simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  · simp only [Matrix.mul_one, hrho.2, Complex.one_re]

/-! ## The base case: dimension one -/

theorem frameRepresentation_one : FrameRepresentation 1 := by
  intro mu hmu
  refine ⟨1, Matrix.isHermitian_one, fun v hv => ?_⟩
  have hv2 : star v ⬝ᵥ v = 1 := hv
  have hv' : (starRingEnd ℂ) (v 0) * v 0 = 1 := by
    simpa [dotProduct, Fin.sum_univ_one] using hv2
  have h1 : rankOneProj v = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp only [rankOneProj, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def,
      Matrix.one_apply_eq]
    rw [mul_comm]
    exact hv'
  rw [h1, one_mul, hmu.normalized, Matrix.trace_one]
  simp

/-- Unconditional Gleason theorem in dimension one. -/
theorem gleason_dim_one (mu : Matrix (Fin 1) (Fin 1) ℂ → ℝ) (hmu : IsQuantumMeasure mu) :
    ∃ rho : Matrix (Fin 1) (Fin 1) ℂ, IsDensityOperator rho ∧
      ∀ P : Matrix (Fin 1) (Fin 1) ℂ, IsProj P → ((mu P : ℝ) : ℂ) = (rho * P).trace :=
  gleason_of_frameRepresentation frameRepresentation_one mu hmu

end Frontier

import RequestProject.Gleason
/-!
# Failure of Gleason's theorem in dimension two

Gleason's theorem needs `dim ≥ 3`.  Here we build, in dimension two, an explicit quantum
measure that does **not** come from a density operator.  Consequently
`Frontier.FrameRepresentation 2` is false, so the hypothesis of `Frontier.gleason_theorem`
genuinely encodes the dimension restriction.
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

lemma proj_eq_one_of_eigenvalues_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P)
    (h : ∀ j, hP.1.eigenvalues j = 1) : P = 1 := by
  conv_lhs => rw [hP.1.spectral_theorem]
  have hd : (Matrix.diagonal (RCLike.ofReal ∘ hP.1.eigenvalues) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext j
    simp [h j]
  rw [hd, map_one]

lemma proj_exists_eigenvalue_one {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P)
    (h : P ≠ 0) : ∃ j, hP.1.eigenvalues j = 1 := by
  by_contra hc
  push_neg at hc
  refine h (hP.1.eigenvalues_eq_zero_iff.mp ?_)
  funext j
  rcases proj_eigenvalues_eq_zero_or_one hP j with hj | hj
  · simpa using hj
  · exact absurd hj (hc j)

lemma proj_eigenvalues_nonneg {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P) (j : Fin n) :
    0 ≤ hP.1.eigenvalues j := by
  rcases proj_eigenvalues_eq_zero_or_one hP j with h | h <;> simp [h]

private lemma fin_two_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma trace2_eq_sum_eigenvalues {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian) :
    P.trace = ((hP.eigenvalues 0 + hP.eigenvalues 1 : ℝ) : ℂ) := by
  rw [hP.trace_eq_sum_eigenvalues, Fin.sum_univ_two]
  norm_cast

/-- In dimension two, two nonzero orthogonal projections must be complementary. -/
lemma proj2_add_eq_one {P Q : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P) (hQ : IsProj Q)
    (hPQ : P * Q = 0) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : P + Q = 1 := by
  have hQP : Q * P = 0 := by
    have h : (P * Q)ᴴ = (0 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by rw [hPQ]
    rwa [Matrix.conjTranspose_mul, hP.1, hQ.1, Matrix.conjTranspose_zero] at h
  have hR : IsProj (P + Q) := by
    refine ⟨Matrix.IsHermitian.add hP.1 hQ.1, ?_⟩
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hPQ, hQP, hP.2, hQ.2]
    abel
  have htr : (P + Q).trace = P.trace + Q.trace := Matrix.trace_add P Q
  have hreal : hR.1.eigenvalues 0 + hR.1.eigenvalues 1
      = (hP.1.eigenvalues 0 + hP.1.eigenvalues 1) + (hQ.1.eigenvalues 0 + hQ.1.eigenvalues 1) := by
    have hc : ((hR.1.eigenvalues 0 + hR.1.eigenvalues 1 : ℝ) : ℂ)
        = (((hP.1.eigenvalues 0 + hP.1.eigenvalues 1) +
            (hQ.1.eigenvalues 0 + hQ.1.eigenvalues 1) : ℝ) : ℂ) := by
      rw [← trace2_eq_sum_eigenvalues hR.1, htr, trace2_eq_sum_eigenvalues hP.1,
        trace2_eq_sum_eigenvalues hQ.1]
      push_cast
      ring
    exact_mod_cast hc
  obtain ⟨jP, hjP⟩ := proj_exists_eigenvalue_one hP hP0
  obtain ⟨jQ, hjQ⟩ := proj_exists_eigenvalue_one hQ hQ0
  have hPge : 1 ≤ hP.1.eigenvalues 0 + hP.1.eigenvalues 1 := by
    rcases fin_two_cases jP with rfl | rfl
    · linarith [proj_eigenvalues_nonneg hP 1, hjP]
    · linarith [proj_eigenvalues_nonneg hP 0, hjP]
  have hQge : 1 ≤ hQ.1.eigenvalues 0 + hQ.1.eigenvalues 1 := by
    rcases fin_two_cases jQ with rfl | rfl
    · linarith [proj_eigenvalues_nonneg hQ 1, hjQ]
    · linarith [proj_eigenvalues_nonneg hQ 0, hjQ]
  have h0 := proj_eigenvalues_eq_zero_or_one hR 0
  have h1 := proj_eigenvalues_eq_zero_or_one hR 1
  refine proj_eq_one_of_eigenvalues_one hR fun j => ?_
  have hboth : hR.1.eigenvalues 0 = 1 ∧ hR.1.eigenvalues 1 = 1 := by
    rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;> rw [e0, e1] at hreal <;>
      refine ⟨?_, ?_⟩ <;> first | assumption | linarith
  rcases fin_two_cases j with rfl | rfl
  · exact hboth.1
  · exact hboth.2

/-! ## The counterexample -/

/-- Tie-breaking rule on nonzero complex numbers: exactly one of `z`, `-z` gets the value `1`. -/
noncomputable def tieBreak (z : ℂ) : ℝ :=
  if 0 < z.re then 1 else if z.re < 0 then 0 else if 0 < z.im then 1 else 0

lemma tieBreak_nonneg (z : ℂ) : 0 ≤ tieBreak z := by
  unfold tieBreak; split_ifs <;> norm_num

lemma tieBreak_add_neg {z : ℂ} (hz : z ≠ 0) : tieBreak z + tieBreak (-z) = 1 := by
  unfold tieBreak
  simp only [Complex.neg_re, Complex.neg_im]
  split_ifs <;>
    first
      | linarith
      | exact absurd (Complex.ext (show z.re = 0 by linarith) (show z.im = 0 by linarith)) hz

/-- A quantum measure on the qubit that is not given by any density operator. -/
noncomputable def qubitMeasure (P : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  if 1 / 2 < (P 0 0).re then 1 else if (P 0 0).re < 1 / 2 then 0 else tieBreak (P 0 1)

lemma qubitMeasure_nonneg (P : Matrix (Fin 2) (Fin 2) ℂ) : 0 ≤ qubitMeasure P := by
  unfold qubitMeasure
  split_ifs
  · norm_num
  · norm_num
  · exact tieBreak_nonneg _

lemma qubitMeasure_zero : qubitMeasure 0 = 0 := by
  unfold qubitMeasure; norm_num

lemma qubitMeasure_one : qubitMeasure 1 = 1 := by
  unfold qubitMeasure; norm_num

/-- For a two-dimensional projection whose `(0,0)` entry has real part `1/2`, the
off-diagonal entry is nonzero. -/
lemma proj2_offdiag_ne_zero {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P)
    (h : (P 0 0).re = 1 / 2) : P 0 1 ≠ 0 := by
  have hherm : (starRingEnd ℂ) (P 0 0) = P 0 0 := by
    have h' := congrFun (congrFun hP.1 0) 0
    simpa [Matrix.conjTranspose_apply] using h'
  have hP00 : P 0 0 = (1 / 2 : ℂ) := by
    have him : (P 0 0).im = 0 := by
      have h' := congrArg Complex.im hherm
      simp only [Complex.conj_im] at h'
      linarith
    exact Complex.ext (by simpa using h) (by simpa using him)
  have h10 : P 1 0 = (starRingEnd ℂ) (P 0 1) := by
    have h' := congrFun (congrFun hP.1 1) 0
    simpa [Matrix.conjTranspose_apply] using h'.symm
  have hmul := congrFun (congrFun hP.2 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hmul
  rw [hP00, h10] at hmul
  intro hz
  rw [hz] at hmul
  simp at hmul

lemma qubitMeasure_add_compl {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P) :
    qubitMeasure P + qubitMeasure (1 - P) = 1 := by
  have hentry : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - P) 0 0 = 1 - P 0 0 := by
    simp [Matrix.sub_apply]
  have hentry' : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - P) 0 1 = -P 0 1 := by
    simp [Matrix.sub_apply]
  have hre : ((1 : ℂ) - P 0 0).re = 1 - (P 0 0).re := by simp
  unfold qubitMeasure
  rw [hentry, hentry', hre]
  split_ifs <;>
    first
      | linarith
      | exact tieBreak_add_neg (proj2_offdiag_ne_zero hP (by linarith))

theorem isQuantumMeasure_qubitMeasure : IsQuantumMeasure qubitMeasure := by
  refine ⟨fun P _ => qubitMeasure_nonneg P, fun P Q hP hQ hPQ => ?_, qubitMeasure_one⟩
  by_cases hP0 : P = 0
  · rw [hP0, zero_add, qubitMeasure_zero, zero_add]
  by_cases hQ0 : Q = 0
  · rw [hQ0, add_zero, qubitMeasure_zero, add_zero]
  have hsum : P + Q = 1 := proj2_add_eq_one hP hQ hPQ hP0 hQ0
  have hQeq : Q = 1 - P := by rw [← hsum]; abel
  rw [hsum, hQeq, qubitMeasure_one]
  exact (qubitMeasure_add_compl hP).symm

/-! ## `qubitMeasure` does not come from a density operator -/

/-- Unit vectors used to defeat any candidate density operator. -/
noncomputable def wPlus : Fin 2 → ℂ := ![4 / 5, 3 / 5]
noncomputable def wMinus : Fin 2 → ℂ := ![4 / 5, -(3 / 5)]
noncomputable def e0 : Fin 2 → ℂ := ![1, 0]

lemma isUnitVec_wPlus : IsUnitVec wPlus := by
  show star wPlus ⬝ᵥ wPlus = 1
  norm_num [wPlus, dotProduct, Fin.sum_univ_two, Complex.ext_iff, map_div₀, map_ofNat]

lemma isUnitVec_wMinus : IsUnitVec wMinus := by
  show star wMinus ⬝ᵥ wMinus = 1
  norm_num [wMinus, dotProduct, Fin.sum_univ_two, Complex.ext_iff, map_div₀, map_ofNat]

lemma isUnitVec_e0 : IsUnitVec e0 := by
  show star e0 ⬝ᵥ e0 = 1
  norm_num [e0, dotProduct, Fin.sum_univ_two]

lemma qubitMeasure_rankOne_e0 : qubitMeasure (rankOneProj e0) = 1 := by
  unfold qubitMeasure
  rw [if_pos]
  norm_num [rankOneProj, Matrix.vecMulVec_apply, e0]

lemma qubitMeasure_rankOne_wPlus : qubitMeasure (rankOneProj wPlus) = 1 := by
  unfold qubitMeasure
  rw [if_pos]
  norm_num [rankOneProj, Matrix.vecMulVec_apply, wPlus, Complex.ext_iff, map_div₀, map_ofNat]

lemma qubitMeasure_rankOne_wMinus : qubitMeasure (rankOneProj wMinus) = 1 := by
  unfold qubitMeasure
  rw [if_pos]
  norm_num [rankOneProj, Matrix.vecMulVec_apply, wMinus, Complex.ext_iff, map_div₀, map_ofNat]

theorem not_exists_density_for_qubitMeasure :
    ¬ ∃ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityOperator rho ∧
      ∀ P : Matrix (Fin 2) (Fin 2) ℂ, IsProj P →
        ((qubitMeasure P : ℝ) : ℂ) = (rho * P).trace := by
  rintro ⟨rho, ⟨-, htr⟩, hrep⟩
  have key : ∀ v : Fin 2 → ℂ, IsUnitVec v →
      ((qubitMeasure (rankOneProj v) : ℝ) : ℂ) = star v ⬝ᵥ (rho *ᵥ v) := fun v hv => by
    rw [hrep _ (isProj_rankOneProj hv), trace_mul_rankOneProj]
  have h0 := key e0 isUnitVec_e0
  have hp := key wPlus isUnitVec_wPlus
  have hm := key wMinus isUnitVec_wMinus
  rw [qubitMeasure_rankOne_e0] at h0
  rw [qubitMeasure_rankOne_wPlus] at hp
  rw [qubitMeasure_rankOne_wMinus] at hm
  simp only [dotProduct, Fin.sum_univ_two, Matrix.mulVec, Pi.star_apply, e0, wPlus, wMinus,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_div₀, map_ofNat,
    RCLike.star_def, map_neg, map_one, map_zero, Complex.ofReal_one] at h0 hp hm
  have hrho00 : rho 0 0 = 1 := by linear_combination -h0
  have hrho11 : rho 1 1 = 0 := by
    have h : rho.trace = rho 0 0 + rho 1 1 := by rw [Matrix.trace, Fin.sum_univ_two]; rfl
    rw [htr, hrho00] at h
    linear_combination -h
  rw [hrho00, hrho11] at hp hm
  have hcontra : (2 : ℂ) = 32 / 25 := by linear_combination hp + hm
  norm_num at hcontra

/-- Gleason's analytic core fails in dimension two. -/
theorem not_frameRepresentation_two : ¬ FrameRepresentation 2 := fun h =>
  not_exists_density_for_qubitMeasure
    (gleason_of_frameRepresentation h qubitMeasure isQuantumMeasure_qubitMeasure)

/-- **The dimension hypothesis in Gleason's theorem is necessary**: in dimension two there is a
quantum measure that does not come from any density operator. -/
theorem exists_quantumMeasure_not_density_dim_two :
    ∃ mu : Matrix (Fin 2) (Fin 2) ℂ → ℝ, IsQuantumMeasure mu ∧
      ¬ ∃ rho : Matrix (Fin 2) (Fin 2) ℂ, IsDensityOperator rho ∧
        ∀ P : Matrix (Fin 2) (Fin 2) ℂ, IsProj P → ((mu P : ℝ) : ℂ) = (rho * P).trace :=
  ⟨qubitMeasure, isQuantumMeasure_qubitMeasure, not_exists_density_for_qubitMeasure⟩

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

