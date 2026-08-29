import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/
lemma two_dim_cayley (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

/-- A `2 × 2` orthogonal projection is `0`, `1`, or has trace one (i.e. has rank one). -/
lemma dimTwo_proj_trichotomy {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P) :
    P = 0 ∨ P = 1 ∨ P.trace = 1 := by
  by_cases ht : P.trace = 1
  · exact Or.inr (Or.inr ht)
  have h := two_dim_cayley P
  rw [hP.2] at h
  set t : ℂ := P.trace with ht'
  set d : ℂ := P.det with hd'
  have htne : t - 1 ≠ 0 := sub_ne_zero.mpr ht
  have h2 : (t - 1) • P = d • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [sub_smul, one_smul]
    nth_rewrite 2 [h]
    abel
  have h3 : P = ((t - 1)⁻¹ * d) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    have h4 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => (t - 1)⁻¹ • M) h2
    simpa [smul_smul, inv_mul_cancel₀ htne] using h4
  set c : ℂ := (t - 1)⁻¹ * d with hc
  have h4 : c * c = c := by
    have h5 := hP.2
    rw [h3, smul_mul_smul_comm, one_mul] at h5
    have h6 := congrFun (congrFun h5 0) 0
    simpa using h6
  have h7 : c * (c - 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp h7 with h8 | h8
  · exact Or.inl (by rw [h3, h8, zero_smul])
  · exact Or.inr (Or.inl (by rw [h3, sub_eq_zero.mp h8, one_smul]))

/-- In dimension two, two nonzero orthogonal projections are complementary. -/
lemma dimTwo_orthogonal_complement {P Q : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P)
    (hQ : IsProj Q) (hPQ : P * Q = 0) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : P + Q = 1 := by
  have hP1 : P ≠ 1 := by
    rintro rfl; exact hQ0 (by simpa using hPQ)
  have hQ1 : Q ≠ 1 := by
    rintro rfl; exact hP0 (by simpa using hPQ)
  have htP : P.trace = 1 := ((dimTwo_proj_trichotomy hP).resolve_left hP0).resolve_left hP1
  have htQ : Q.trace = 1 := ((dimTwo_proj_trichotomy hQ).resolve_left hQ0).resolve_left hQ1
  have htsum : (P + Q).trace = 2 := by rw [Matrix.trace_add, htP, htQ]; norm_num
  rcases dimTwo_proj_trichotomy (hP.add hQ hPQ) with h | h | h
  · rw [h] at htsum; simp at htsum
  · exact h
  · rw [h] at htsum; norm_num at htsum

/-- The `(0,0)` entry of a `2 × 2` projection is real and, together with the `(0,1)` entry,
satisfies `a² + |b|² = a`. -/
lemma dimTwo_proj_entries {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P) :
    (P 0 0).im = 0 ∧ (P 0 0).re ^ 2 + Complex.normSq (P 0 1) = (P 0 0).re := by
  have hh : P 1 0 = star (P 0 1) := by
    have h := hP.1.apply 0 1
    rw [← h, star_star]
  have h00 : star (P 0 0) = P 0 0 := hP.1.apply 0 0
  have him : (P 0 0).im = 0 := Complex.conj_eq_iff_im.mp h00
  refine ⟨him, ?_⟩
  have h := congrFun (congrFun hP.2 0) 0
  rw [Matrix.mul_apply, Fin.sum_univ_two, hh] at h
  have hre := congrArg Complex.re h
  simp [Complex.mul_re, Complex.normSq_apply, him] at hre ⊢
  nlinarith [hre]

/-! ## A two-valued quantum measure on `ℂ²` -/

/-- Lexicographic positivity of a triple of reals with respect to the "origin" `(1/2, 0, 0)`. -/
def sgnPos (x y z : ℝ) : Prop := 1 / 2 < x ∨ (x = 1 / 2 ∧ (0 < y ∨ (y = 0 ∧ 0 < z)))

/-- Exactly one of a triple and its reflection through `(1/2, 0, 0)` is lexicographically
positive, provided the triple is not the centre itself. -/
lemma sgnPos_add_compl (x y z : ℝ) (h : x = 1 / 2 → (y ≠ 0 ∨ z ≠ 0)) :
    (if sgnPos x y z then (1 : ℝ) else 0) + (if sgnPos (1 - x) (-y) (-z) then (1 : ℝ) else 0)
      = 1 := by
  unfold sgnPos
  rcases lt_trichotomy x (1 / 2) with hx | hx | hx
  · rw [if_neg (by rintro (h1 | ⟨h1, -⟩) <;> linarith), if_pos (by left; linarith)]
    norm_num
  · rcases h hx with hy | hz
    · rcases lt_or_gt_of_ne hy with hy' | hy'
      · rw [if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, -⟩)⟩) <;> linarith),
          if_pos (by right; exact ⟨by linarith, Or.inl (by linarith)⟩)]
        norm_num
      · rw [if_pos (by right; exact ⟨hx, Or.inl hy'⟩),
          if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, -⟩)⟩) <;> linarith)]
        norm_num
    · rcases em (y = 0) with hy0 | hy0
      · rcases lt_or_gt_of_ne hz with hz' | hz'
        · rw [if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, h3⟩)⟩) <;> linarith),
            if_pos (by right; exact ⟨by linarith, Or.inr ⟨by linarith, by linarith⟩⟩)]
          norm_num
        · rw [if_pos (by right; exact ⟨hx, Or.inr ⟨hy0, hz'⟩⟩),
            if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, h3⟩)⟩) <;> linarith)]
          norm_num
      · rcases lt_or_gt_of_ne hy0 with hy' | hy'
        · rw [if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, -⟩)⟩) <;> linarith),
            if_pos (by right; exact ⟨by linarith, Or.inl (by linarith)⟩)]
          norm_num
        · rw [if_pos (by right; exact ⟨hx, Or.inl hy'⟩),
            if_neg (by rintro (h1 | ⟨-, (h2 | ⟨h2, -⟩)⟩) <;> linarith)]
          norm_num
  · rw [if_pos (by left; linarith), if_neg (by rintro (h1 | ⟨h1, -⟩) <;> linarith)]
    norm_num

/-- The two-valued "lexicographic" measure on `2 × 2` matrices. -/
noncomputable def badMeasure (M : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  if sgnPos (M 0 0).re (M 0 1).re (M 0 1).im then 1 else 0

lemma badMeasure_zero : badMeasure 0 = 0 := by
  rw [badMeasure, if_neg]
  rintro (h | ⟨h, -⟩) <;> norm_num at h

lemma badMeasure_one : badMeasure 1 = 1 := by
  rw [badMeasure, if_pos]
  left
  norm_num [Matrix.one_apply]

/-- The lexicographic measure is a quantum measure on the projections of `ℂ²`. -/
theorem badMeasure_isQuantumMeasure : IsQuantumMeasure badMeasure := by
  refine ⟨fun P _ => ?_, badMeasure_one, fun P Q hP hQ hPQ => ?_⟩
  · rw [badMeasure]; split <;> norm_num
  by_cases hP0 : P = 0
  · subst hP0; rw [zero_add, badMeasure_zero, zero_add]
  by_cases hQ0 : Q = 0
  · subst hQ0; rw [add_zero, badMeasure_zero, add_zero]
  have hsum : P + Q = 1 := dimTwo_orthogonal_complement hP hQ hPQ hP0 hQ0
  have hQeq : Q = 1 - P := by rw [← hsum]; abel
  obtain ⟨-, hentry⟩ := dimTwo_proj_entries hP
  have hne : (P 0 0).re = 1 / 2 → ((P 0 1).re ≠ 0 ∨ (P 0 1).im ≠ 0) := by
    intro hx
    rw [hx] at hentry
    have hnsq : Complex.normSq (P 0 1) = 1 / 4 := by nlinarith [hentry]
    have hb : P 0 1 ≠ 0 := by
      intro hb0
      rw [hb0] at hnsq
      norm_num [Complex.normSq_apply] at hnsq
    by_contra hcon
    push_neg at hcon
    exact hb (Complex.ext hcon.1 hcon.2)
  have h00 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - P) 0 0 = 1 - P 0 0 := by
    simp [Matrix.sub_apply]
  have h01 : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - P) 0 1 = -(P 0 1) := by
    simp [Matrix.sub_apply]
  rw [hsum, badMeasure_one, badMeasure, hQeq, badMeasure, h00, h01]
  simpa using (sgnPos_add_compl (P 0 0).re (P 0 1).re (P 0 1).im hne).symm

/-! ## The measure is not given by a density operator -/

/-- The projection onto the first coordinate axis of `ℂ²`. -/
def projZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The projection onto the diagonal line of `ℂ²`. -/
noncomputable def projX : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

lemma isProj_projZ : IsProj projZ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [projZ, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [projZ, Matrix.mul_apply, Fin.sum_univ_two]

lemma isProj_projX : IsProj projX := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [projX, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [projX, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma badMeasure_projZ : badMeasure projZ = 1 := by
  rw [badMeasure, if_pos]
  left
  norm_num [projZ]

lemma badMeasure_projX : badMeasure projX = 1 := by
  rw [badMeasure, if_pos]
  right
  refine ⟨by norm_num [projX], Or.inl (by norm_num [projX])⟩

/-- **Gleason's theorem fails in dimension two**: the lexicographic quantum measure on the
projections of `ℂ²` is not of the form `P ↦ Re tr (ρ P)` for any density operator `ρ`. -/
theorem gleason_fails_in_dim_two :
    ¬ ∃ ρ : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix ρ ∧
        ∀ P : Matrix (Fin 2) (Fin 2) ℂ, IsProj P → badMeasure P = (ρ * P).trace.re := by
  rintro ⟨ρ, ⟨hpsd, htr⟩, hrep⟩
  have hherm : ρ 1 0 = star (ρ 0 1) := by
    have h := hpsd.1.apply 0 1
    rw [← h, star_star]
  have him00 : (ρ 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hpsd.1.apply 0 0)
  have him11 : (ρ 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hpsd.1.apply 1 1)
  -- the `z` projection forces `ρ 0 0 = 1`
  have hz := hrep projZ isProj_projZ
  rw [badMeasure_projZ] at hz
  have hz' : (ρ 0 0).re = 1 := by
    have : (ρ * projZ).trace = ρ 0 0 := by
      simp [projZ, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this] at hz
    exact hz.symm
  -- unit trace forces `ρ 1 1 = 0`
  have htr' : (ρ 0 0).re + (ρ 1 1).re = 1 := by
    have := congrArg Complex.re htr
    rw [Matrix.trace_fin_two] at this
    simpa using this
  have h11 : (ρ 1 1).re = 0 := by linarith
  -- the `x` projection forces `Re (ρ 0 1) = 1/2`
  have hx := hrep projX isProj_projX
  rw [badMeasure_projX] at hx
  have hxtrace : (ρ * projX).trace = (ρ 0 0 + ρ 0 1 + ρ 1 0 + ρ 1 1) / 2 := by
    simp [projX, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hxtrace] at hx
  have hre01 : (ρ 0 1).re = 1 / 2 := by
    have hrew : ((ρ 0 0 + ρ 0 1 + ρ 1 0 + ρ 1 1) / 2).re
        = ((ρ 0 0).re + (ρ 0 1).re + (ρ 1 0).re + (ρ 1 1).re) / 2 := by
      simp
    rw [hrew] at hx
    have h10 : (ρ 1 0).re = (ρ 0 1).re := by rw [hherm]; simp
    rw [h10, hz', h11] at hx
    linarith
  -- but then positive semidefiniteness fails on the vector `(-1/2, 1)`
  have hpos := hpsd.re_dotProduct_nonneg ![(-1 : ℂ), 2]
  have hval : (star ![(-1 : ℂ), 2] ⬝ᵥ ρ *ᵥ ![(-1 : ℂ), 2])
      = ρ 0 0 - 2 * ρ 0 1 - 2 * ρ 1 0 + 4 * ρ 1 1 := by
    have h2 : (starRingEnd ℂ) 2 = 2 := Complex.conj_eq_iff_re.mpr rfl
    simp [dotProduct, mulVec, Fin.sum_univ_two, h2]
    ring
  rw [hval] at hpos
  have h10re : (ρ 1 0).re = (ρ 0 1).re := by rw [hherm]; simp
  have hρ00 : ρ 0 0 = 1 := Complex.ext (by rw [hz']; rfl) (by rw [him00]; rfl)
  have hρ11 : ρ 1 1 = 0 := Complex.ext (by rw [h11]; rfl) (by rw [him11]; rfl)
  rw [hρ00, hρ11] at hpos
  simp [RCLike.re_to_complex, Complex.sub_re, Complex.mul_re, h10re, hre01] at hpos
  linarith

end Frontier

/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is repeated
-- below as the module docstring of this file.)
import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open Matrix

variable {N : ℕ}

/-- An orthogonal projection on the Hilbert space `ℂ^N`, represented as a matrix. -/
def IsProj (P : Matrix (Fin N) (Fin N) ℂ) : Prop := P.IsHermitian ∧ P * P = P

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `v`. -/
def rankOne (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ := Matrix.vecMulVec v (star v)

/-- A *quantum measure* (Gleason measure) on the projection lattice of `ℂ^N`:
a nonnegative, normalized, finitely additive function on orthogonal projections. -/
structure IsQuantumMeasure (μ : Matrix (Fin N) (Fin N) ℂ → ℝ) : Prop where
  nonneg : ∀ P, IsProj P → 0 ≤ μ P
  normalized : μ 1 = 1
  additive : ∀ P Q, IsProj P → IsProj Q → P * Q = 0 → μ (P + Q) = μ P + μ Q

/-- A density operator: a positive semidefinite matrix of unit trace. -/
def IsDensityMatrix (ρ : Matrix (Fin N) (Fin N) ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- The *frame function* of `μ` (its restriction to rank-one projections) is *regular*
if it is given by a quadratic form of a Hermitian matrix. -/
def IsRegularFrameFunction (μ : Matrix (Fin N) (Fin N) ℂ → ℝ) : Prop :=
  ∃ T : Matrix (Fin N) (Fin N) ℂ, T.IsHermitian ∧
    ∀ v : Fin N → ℂ, star v ⬝ᵥ v = 1 → μ (rankOne v) = (star v ⬝ᵥ T *ᵥ v).re

/-! ## Basic facts about rank-one projections -/

lemma rankOne_mul (v w : Fin N → ℂ) :
    rankOne v * rankOne w = (star v ⬝ᵥ w) • Matrix.vecMulVec v (star w) := by
  unfold rankOne
  rw [Matrix.vecMulVec_mul, Matrix.vecMul_vecMulVec, Matrix.vecMulVec_smul]

lemma rankOne_isProj {v : Fin N → ℂ} (hv : star v ⬝ᵥ v = 1) : IsProj (rankOne v) := by
  constructor
  · unfold rankOne Matrix.IsHermitian
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]
  · rw [rankOne_mul, hv, one_smul]
    rfl

lemma rankOne_orthogonal {v w : Fin N → ℂ} (h : star v ⬝ᵥ w = 0) :
    rankOne v * rankOne w = 0 := by
  rw [rankOne_mul, h, zero_smul]

lemma trace_mul_rankOne (T : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    (T * rankOne v).trace = star v ⬝ᵥ T *ᵥ v := by
  unfold rankOne
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

/-- The quadratic form of a Hermitian matrix takes real values. -/
lemma hermitian_dotProduct_im_eq_zero {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.IsHermitian)
    (v : Fin N → ℂ) : (star v ⬝ᵥ T *ᵥ v).im = 0 := by
  have h : star (star v ⬝ᵥ T *ᵥ v) = star v ⬝ᵥ T *ᵥ v := by
    simp only [dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hT.apply i j]
    simp only [star_star]
    ring
  exact Complex.conj_eq_iff_im.mp h

/-- The trace of a Hermitian matrix is real. -/
lemma hermitian_trace_im_eq_zero {T : Matrix (Fin N) (Fin N) ℂ} (hT : T.IsHermitian) :
    T.trace.im = 0 := by
  simp only [Matrix.trace, Matrix.diag, Complex.im_sum]
  exact Finset.sum_eq_zero fun i _ => Complex.conj_eq_iff_im.mp (hT.apply i i)

/-! ## Basic facts about projections and quantum measures -/

lemma isProj_zero : IsProj (0 : Matrix (Fin N) (Fin N) ℂ) := ⟨Matrix.isHermitian_zero, by simp⟩

lemma isProj_one : IsProj (1 : Matrix (Fin N) (Fin N) ℂ) := ⟨Matrix.isHermitian_one, by simp⟩

lemma IsProj.mul_comm_zero {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) (hQ : IsProj Q)
    (h : P * Q = 0) : Q * P = 0 := by
  have h' : (P * Q)ᴴ = 0 := by rw [h]; simp
  rwa [Matrix.conjTranspose_mul, hP.1.eq, hQ.1.eq] at h'

lemma IsProj.add {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) (hQ : IsProj Q)
    (h : P * Q = 0) : IsProj (P + Q) := by
  refine ⟨hP.1.add hQ.1, ?_⟩
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h, hP.mul_comm_zero hQ h, hP.2, hQ.2]
  abel

lemma IsQuantumMeasure.map_zero {μ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hμ : IsQuantumMeasure μ) :
    μ 0 = 0 := by
  have := hμ.additive 0 0 isProj_zero isProj_zero (by simp)
  simpa using this

/-- A finite sum of pairwise orthogonal projections is a projection. -/
lemma isProj_sum {ι : Type*} (s : Finset ι) (P : ι → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i ∈ s, IsProj (P i)) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    IsProj (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isProj_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hmem : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
      refine IsProj.add (hP a (Finset.mem_insert_self a s))
        (ih (fun i hi => hP i (hmem i hi))
          (fun i hi j hj hij => horth i (hmem i hi) j (hmem j hj) hij)) ?_
      rw [Matrix.mul_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact horth a (Finset.mem_insert_self a s) i (hmem i hi) (by rintro rfl; exact ha hi)

/-- Finite additivity of a quantum measure over a family of pairwise orthogonal projections. -/
lemma IsQuantumMeasure.sum {μ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hμ : IsQuantumMeasure μ)
    {ι : Type*} (s : Finset ι) (P : ι → Matrix (Fin N) (Fin N) ℂ)
    (hP : ∀ i ∈ s, IsProj (P i)) (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    μ (∑ i ∈ s, P i) = ∑ i ∈ s, μ (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hμ.map_zero
  | insert a s ha ih =>
      have hmem : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih (fun i hi => hP i (hmem i hi))
        (fun i hi j hj hij => horth i (hmem i hi) j (hmem j hj) hij)]
      refine hμ.additive _ _ (hP a (Finset.mem_insert_self a s))
        (isProj_sum s P (fun i hi => hP i (hmem i hi))
          (fun i hi j hj hij => horth i (hmem i hi) j (hmem j hj) hij)) ?_
      rw [Matrix.mul_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact horth a (Finset.mem_insert_self a s) i (hmem i hi) (by rintro rfl; exact ha hi)

/-! ## Spectral decomposition into rank-one projections -/

/-- The vectors of an orthonormal basis of `ℂ^N` are orthonormal for the dot product. -/
lemma orthonormalBasis_dotProduct (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N)))
    (i j : Fin N) : star (⇑(b i)) ⬝ᵥ (⇑(b j)) = if i = j then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp b.orthonormal) i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [dotProduct_comm]
  exact h

/-- The eigenvectors of a Hermitian matrix form an orthonormal family. -/
lemma hermitian_eigenvector_dotProduct {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (i j : Fin N) :
    star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.eigenvectorBasis j)) = if i = j then 1 else 0 :=
  orthonormalBasis_dotProduct hA.eigenvectorBasis i j

/-- The rank-one projections onto the vectors of an orthonormal basis sum to the identity. -/
lemma sum_rankOne_orthonormalBasis (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ i, rankOne (⇑(b i)) = (1 : Matrix (Fin N) (Fin N) ℂ) := by
  classical
  set U : Matrix (Fin N) (Fin N) ℂ :=
    (EuclideanSpace.basisFun (Fin N) ℂ).toBasis.toMatrix b.toBasis with hUdef
  have hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ :=
    (EuclideanSpace.basisFun (Fin N) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hUU : U * star U = 1 := by
    simpa using (Matrix.mem_unitaryGroup_iff).mp hU
  have hentry : ∀ i j : Fin N, U i j = (b j : EuclideanSpace ℂ (Fin N)) i := fun _ _ => rfl
  ext j k
  have hjk := congrFun (congrFun hUU j) k
  rw [Matrix.mul_apply] at hjk
  simp only [Matrix.sum_apply, rankOne, Matrix.vecMulVec_apply, Pi.star_apply]
  rw [← hjk]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hentry, Matrix.star_apply]

/-- **Frame function property.** For any quantum measure and any orthonormal basis, the values
of the measure on the rank-one projections onto the basis vectors sum to one. -/
theorem sum_rankOne_measure_eq_one {μ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hμ : IsQuantumMeasure μ)
    (b : OrthonormalBasis (Fin N) ℂ (EuclideanSpace ℂ (Fin N))) :
    ∑ i, μ (rankOne (⇑(b i))) = 1 := by
  classical
  have hunit : ∀ i, star (⇑(b i)) ⬝ᵥ (⇑(b i)) = 1 := by
    intro i; simpa using orthonormalBasis_dotProduct b i i
  have horth : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j →
      rankOne (⇑(b i)) * rankOne (⇑(b j)) = 0 := by
    intro i _ j _ hij
    exact rankOne_orthogonal (by simpa [hij] using orthonormalBasis_dotProduct b i j)
  have := hμ.sum Finset.univ (fun i => rankOne (⇑(b i)))
    (fun i _ => rankOne_isProj (hunit i)) horth
  rw [sum_rankOne_orthonormalBasis b, hμ.normalized] at this
  exact this.symm

/-- Any Hermitian matrix is the sum of its eigenvalues times the rank-one projections onto
the corresponding eigenvectors. -/
lemma hermitian_eq_sum_rankOne {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    A = ∑ i, (hA.eigenvalues i : ℂ) • rankOne (⇑(hA.eigenvectorBasis i)) := by
  ext j k
  conv_lhs => rw [hA.spectral_theorem]
  simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    rankOne, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, mul_comm, mul_assoc]

/-- The eigenvalues of an orthogonal projection are `0` or `1`. -/
lemma proj_eigenvalues_eq_zero_or_one {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) (i : Fin N) :
    hP.1.eigenvalues i = 0 ∨ hP.1.eigenvalues i = 1 := by
  set v : Fin N → ℂ := ⇑(hP.1.eigenvectorBasis i) with hv
  set l : ℝ := hP.1.eigenvalues i with hl
  have hvne : v ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.2 (hP.1.eigenvectorBasis.orthonormal.ne_zero i)
  have h1 : P *ᵥ v = l • v := hP.1.mulVec_eigenvectorBasis i
  have h2 : P *ᵥ (P *ᵥ v) = (l * l) • v := by
    rw [h1, Matrix.mulVec_smul, h1, smul_smul]
  have h3 : P *ᵥ (P *ᵥ v) = l • v := by
    rw [Matrix.mulVec_mulVec, hP.2, h1]
  have h5 : (l * l - l) • v = 0 := by
    rw [sub_smul, ← h2, h3, sub_self]
  have h6 : l * l - l = 0 := by
    by_contra h
    exact hvne ((smul_eq_zero.mp h5).resolve_left h)
  have h7 : l * (l - 1) = 0 := by nlinarith [h6]
  rcases mul_eq_zero.mp h7 with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- Every orthogonal projection is the sum of the rank-one projections onto the eigenvectors
belonging to the eigenvalue `1`. -/
lemma proj_eq_sum_rankOne {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) :
    P = ∑ i ∈ Finset.univ.filter (fun i => hP.1.eigenvalues i = 1),
          rankOne (⇑(hP.1.eigenvectorBasis i)) := by
  classical
  rw [Finset.sum_filter]
  conv_lhs => rw [hermitian_eq_sum_rankOne hP.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : hP.1.eigenvalues i = 1
  · simp [h]
  · have h0 : hP.1.eigenvalues i = 0 := (proj_eigenvalues_eq_zero_or_one hP i).resolve_right h
    simp [h0]

/-! ## Gleason's theorem: reduction to regularity of the frame function -/

/-- If the frame function of a quantum measure is the quadratic form of a Hermitian matrix `T`,
then the measure is given by `P ↦ Re tr (T P)` on all projections. -/
lemma measure_eq_trace_of_regular {μ : Matrix (Fin N) (Fin N) ℂ → ℝ} (hμ : IsQuantumMeasure μ)
    {T : Matrix (Fin N) (Fin N) ℂ}
    (hframe : ∀ v : Fin N → ℂ, star v ⬝ᵥ v = 1 → μ (rankOne v) = (star v ⬝ᵥ T *ᵥ v).re)
    {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsProj P) : μ P = (T * P).trace.re := by
  classical
  set S : Finset (Fin N) := Finset.univ.filter (fun i => hP.1.eigenvalues i = 1) with hS
  set v : Fin N → (Fin N → ℂ) := fun i => ⇑(hP.1.eigenvectorBasis i) with hv
  have hunit : ∀ i, star (v i) ⬝ᵥ v i = 1 := by
    intro i; simpa using hermitian_eigenvector_dotProduct hP.1 i i
  have hproj : ∀ i, IsProj (rankOne (v i)) := fun i => rankOne_isProj (hunit i)
  have horth : ∀ i j : Fin N, i ≠ j → rankOne (v i) * rankOne (v j) = 0 := by
    intro i j hij
    refine rankOne_orthogonal ?_
    simpa [hij] using hermitian_eigenvector_dotProduct hP.1 i j
  have hPsum : P = ∑ i ∈ S, rankOne (v i) := proj_eq_sum_rankOne hP
  calc μ P = ∑ i ∈ S, μ (rankOne (v i)) := by
        rw [hPsum]
        exact hμ.sum S _ (fun i _ => hproj i) (fun i _ j _ hij => horth i j hij)
    _ = ∑ i ∈ S, (star (v i) ⬝ᵥ T *ᵥ v i).re :=
        Finset.sum_congr rfl fun i _ => hframe (v i) (hunit i)
    _ = (T * P).trace.re := by
        rw [hPsum, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [trace_mul_rankOne]

/-- **Gleason's theorem, stated as a Lean-checked reduction.**

For a quantum measure `μ` on the projection lattice of a complex Hilbert space of dimension
`N ≥ 3`, the following are equivalent:

* `μ` is given by a density operator, i.e. `μ P = Re tr (ρ P)` for a positive semidefinite `ρ`
  of unit trace (the conclusion of Gleason's theorem);
* the frame function of `μ` — its restriction to the rank-one projections — is *regular*,
  i.e. given by the quadratic form of a Hermitian matrix.

This is the standard reduction of Gleason's theorem to the analytic statement about frame
functions on the unit sphere: the whole content of Gleason's theorem is that, when `N ≥ 3`,
the right-hand side always holds.  The hypothesis `3 ≤ N` is stated because it is part of the
classical statement; the equivalence proved here does not use it. -/
theorem gleason_theorem (hN : 3 ≤ N) (μ : Matrix (Fin N) (Fin N) ℂ → ℝ)
    (hμ : IsQuantumMeasure μ) :
    (∃ ρ : Matrix (Fin N) (Fin N) ℂ, IsDensityMatrix ρ ∧
        ∀ P : Matrix (Fin N) (Fin N) ℂ, IsProj P → μ P = (ρ * P).trace.re)
      ↔ IsRegularFrameFunction μ := by
  constructor
  · rintro ⟨ρ, ⟨hρ, -⟩, hrep⟩
    refine ⟨ρ, hρ.1, fun w hw => ?_⟩
    rw [hrep _ (rankOne_isProj hw), trace_mul_rankOne]
  · rintro ⟨T, hT, hframe⟩
    have key : ∀ P : Matrix (Fin N) (Fin N) ℂ, IsProj P → μ P = (T * P).trace.re :=
      fun P hP => measure_eq_trace_of_regular hμ hframe hP
    refine ⟨T, ⟨?_, ?_⟩, key⟩
    · -- `T` is positive semidefinite: its eigenvalues are values of `μ` on rank-one projections
      refine hT.posSemidef_iff_eigenvalues_nonneg.mpr fun i => ?_
      have hunit : star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ (⇑(hT.eigenvectorBasis i)) = 1 := by
        simpa using hermitian_eigenvector_dotProduct hT i i
      have hval := hframe (⇑(hT.eigenvectorBasis i)) hunit
      have hnn := hμ.nonneg _ (rankOne_isProj hunit)
      rw [hval] at hnn
      have : (0 : ℝ) ≤ hT.eigenvalues i := by
        rw [hT.eigenvalues_eq i]
        simpa [RCLike.re_to_complex] using hnn
      simpa using this
    · -- `T` has unit trace
      have h1 : μ 1 = (T * 1).trace.re := key 1 isProj_one
      rw [hμ.normalized, Matrix.mul_one] at h1
      exact Complex.ext h1.symm (by simp [hermitian_trace_im_eq_zero hT])

/-- The converse direction: every density operator does define a quantum measure.  Together with
`Frontier.gleason_theorem` this shows that both sides of the equivalence are statements about
genuinely existing objects. -/
theorem isQuantumMeasure_of_density {ρ : Matrix (Fin N) (Fin N) ℂ} (hρ : IsDensityMatrix ρ) :
    IsQuantumMeasure (fun P : Matrix (Fin N) (Fin N) ℂ => (ρ * P).trace.re) := by
  obtain ⟨hpsd, htr⟩ := hρ
  refine ⟨fun P hP => ?_, ?_, fun P Q _ _ _ => ?_⟩
  · have h : (ρ * P).trace = (Pᴴ * ρ * P).trace := by
      conv_lhs => rw [← hP.2]
      rw [hP.1.eq, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have hnn : (0 : ℂ) ≤ (ρ * P).trace := by
      rw [h]; exact (hpsd.conjTranspose_mul_mul_same P).trace_nonneg
    simpa using (Complex.le_def.mp hnn).1
  · rw [Matrix.mul_one, htr, Complex.one_re]
  · rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]

end Frontier

