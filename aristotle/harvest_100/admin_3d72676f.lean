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

import Mathlib
/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires the `import` line to precede any module doc comment, so the
-- header block above appears immediately after the single required import.)

open scoped BigOperators
open scoped Real

namespace Brockian

open Matrix

/-! ## The trace norm of a Hermitian matrix -/

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/
noncomputable def hermTraceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

end Defs

/-! ## Rank-one projections -/

section RankOne

variable {n : Type*} [Fintype n]

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `u`. -/
def rankOneProj (u : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec u (star u)

/-- The Hermitian inner product on `ℂⁿ`, conjugate-linear in the first variable. -/
noncomputable def inn (u v : n → ℂ) : ℂ := ∑ k, star (u k) * v k

lemma inn_swap (u v : n → ℂ) : inn v u = star (inn u v) := by
  simp [inn, mul_comm]

lemma mul_star_eq_normSq (c : ℂ) : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  rw [show star c = (starRingEnd ℂ) c from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma vecMulVec_mul_vecMulVec (a b c d : n → ℂ) :
    Matrix.vecMulVec a b * Matrix.vecMulVec c d
      = (∑ k, b k * c k) • Matrix.vecMulVec a d := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma trace_vecMulVec (a b : n → ℂ) :
    (Matrix.vecMulVec a b).trace = ∑ k, a k * b k := by
  simp [Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply]

omit [Fintype n] in
lemma rankOneProj_isHermitian (u : n → ℂ) : (rankOneProj u).IsHermitian := by
  ext i j
  simp [rankOneProj, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

omit [Fintype n] in
/-- The difference of two rank-one projections is Hermitian. -/
lemma projDiff_isHermitian (u v : n → ℂ) :
    (rankOneProj u - rankOneProj v).IsHermitian :=
  (rankOneProj_isHermitian u).sub (rankOneProj_isHermitian v)

lemma proj_mul_proj (u v : n → ℂ) :
    rankOneProj u * rankOneProj v = inn u v • Matrix.vecMulVec u (star v) := by
  rw [rankOneProj, rankOneProj, vecMulVec_mul_vecMulVec]; rfl

lemma proj_mul_self {u : n → ℂ} (hu : inn u u = 1) :
    rankOneProj u * rankOneProj u = rankOneProj u := by
  rw [proj_mul_proj, hu, one_smul]; rfl

/-- `P Q P = |⟪u,v⟫|² P` for rank-one projections `P`, `Q`. -/
lemma proj_mul_proj_mul_proj (u v : n → ℂ) :
    rankOneProj u * rankOneProj v * rankOneProj u
      = ((‖inn u v‖ ^ 2 : ℝ) : ℂ) • rankOneProj u := by
  rw [proj_mul_proj, smul_mul_assoc, rankOneProj, vecMulVec_mul_vecMulVec]
  have h1 : (∑ k, star v k * u k) = star (inn u v) := by rw [← inn_swap]; rfl
  rw [h1, smul_smul, mul_star_eq_normSq]

lemma trace_rankOneProj (u : n → ℂ) : (rankOneProj u).trace = inn u u := by
  rw [rankOneProj, trace_vecMulVec]; simp [inn, mul_comm]

lemma trace_proj_mul_proj (u v : n → ℂ) :
    (rankOneProj u * rankOneProj v).trace = ((‖inn u v‖ ^ 2 : ℝ) : ℂ) := by
  rw [proj_mul_proj, Matrix.trace_smul, trace_vecMulVec]
  have h1 : (∑ k, u k * star v k) = star (inn u v) := by
    rw [← inn_swap]; simp [inn, mul_comm]
  rw [h1, smul_eq_mul, mul_star_eq_normSq]

lemma norm_inn_swap (u v : n → ℂ) : ‖inn v u‖ = ‖inn u v‖ := by
  rw [inn_swap, norm_star]

/-- The cube of the difference of two rank-one projections is a multiple of itself. -/
lemma projDiff_cube {u v : n → ℂ} (hu : inn u u = 1) (hv : inn v v = 1) :
    (rankOneProj u - rankOneProj v) * (rankOneProj u - rankOneProj v)
        * (rankOneProj u - rankOneProj v)
      = ((1 - ‖inn u v‖ ^ 2 : ℝ) : ℂ) • (rankOneProj u - rankOneProj v) := by
  set P := rankOneProj u
  set Q := rankOneProj v
  have hPP : P * P = P := proj_mul_self hu
  have hQQ : Q * Q = Q := proj_mul_self hv
  have hPQP : P * Q * P = ((‖inn u v‖ ^ 2 : ℝ) : ℂ) • P := proj_mul_proj_mul_proj u v
  have hQPQ : Q * P * Q = ((‖inn u v‖ ^ 2 : ℝ) : ℂ) • Q := by
    rw [proj_mul_proj_mul_proj v u, norm_inn_swap]
  have e : (P - Q) * (P - Q) * (P - Q) =
      P*P*P - P*P*Q - P*Q*P + P*Q*Q - Q*P*P + Q*P*Q + Q*Q*P - Q*Q*Q := by noncomm_ring
  rw [e, hPQP, hQPQ, hPP, mul_assoc P Q Q, hQQ, mul_assoc Q P P, hPP, hQQ]
  push_cast
  module

/-- The trace of the square of the difference of two rank-one projections. -/
lemma projDiff_trace_sq {u v : n → ℂ} (hu : inn u u = 1) (hv : inn v v = 1) :
    ((rankOneProj u - rankOneProj v) * (rankOneProj u - rankOneProj v)).trace
      = ((2 * (1 - ‖inn u v‖ ^ 2) : ℝ) : ℂ) := by
  set P := rankOneProj u
  set Q := rankOneProj v
  have hPP : P * P = P := proj_mul_self hu
  have hQQ : Q * Q = Q := proj_mul_self hv
  have e : (P - Q) * (P - Q) = P*P - P*Q - Q*P + Q*Q := by noncomm_ring
  rw [e, hPP, hQQ]
  rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, trace_rankOneProj,
    trace_rankOneProj, hu, hv, trace_proj_mul_proj, trace_proj_mul_proj, norm_inn_swap]
  push_cast
  ring

end RankOne

/-! ## Spectral input -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eigenvalues of a Hermitian matrix satisfying `A³ = t • A` satisfy `λ³ = t λ`. -/
lemma eigenvalues_cube {A : Matrix n n ℂ} (hA : A.IsHermitian) {t : ℝ}
    (h : A * A * A = (t : ℂ) • A) (i : n) :
    (hA.eigenvalues i) ^ 3 = t * hA.eigenvalues i := by
  set w : n → ℂ := ⇑(hA.eigenvectorBasis i) with hw
  set l := hA.eigenvalues i with hl
  have hAw : A *ᵥ w = l • w := hA.mulVec_eigenvectorBasis i
  have hwne : w ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i
  have e1 : A *ᵥ (A *ᵥ (A *ᵥ w)) = (l ^ 3) • w := by
    simp only [hAw, Matrix.mulVec_smul, smul_smul]
    congr 1
    ring
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc, ← mul_assoc, h,
    Matrix.smul_mulVec, hAw] at e1
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hwne
  have hc := congrFun e1 j
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul] at hc
  have h2 : ((t * l : ℝ) : ℂ) = ((l ^ 3 : ℝ) : ℂ) :=
    mul_right_cancel₀ hj (by push_cast at hc ⊢; linear_combination hc)
  exact_mod_cast h2.symm

/-- The trace of `A * A` is the sum of the squares of the eigenvalues of `A`. -/
lemma trace_mul_self_eq_sum_sq_eigenvalues {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ((hA.eigenvalues i : ℂ) ^ 2) := by
  have hs := hA.spectral_theorem
  set U := hA.eigenvectorUnitary with hU
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have h2 : A * A = Unitary.conjStarAlgAut ℂ _ U (D * D) := by rw [map_mul, ← hs]
  rw [h2, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, ← mul_assoc,
    Unitary.coe_star_mul_self U, one_mul, hD, Matrix.diagonal_mul_diagonal]
  simp [Matrix.trace_diagonal, sq]

/-- Sum of the squares of the eigenvalues of a Hermitian matrix, as a real identity. -/
lemma sum_sq_eigenvalues_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) {r : ℝ}
    (htr : (A * A).trace = (r : ℂ)) : ∑ i, (hA.eigenvalues i) ^ 2 = r := by
  have h1 := trace_mul_self_eq_sum_sq_eigenvalues hA
  rw [htr] at h1
  have h2 : ((r : ℝ) : ℂ) = ((∑ i, (hA.eigenvalues i) ^ 2 : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h2.symm

/-- Key structural computation: a Hermitian matrix `A` with `A³ = s² A` and `tr(A²) = 2 s²`
(for `s ≥ 0`) has trace norm `2 s`. -/
lemma hermTraceNorm_of_cube {A : Matrix n n ℂ} (hA : A.IsHermitian) {s : ℝ} (hs : 0 ≤ s)
    (hcube : A * A * A = ((s ^ 2 : ℝ) : ℂ) • A)
    (htr : (A * A).trace = ((2 * s ^ 2 : ℝ) : ℂ)) :
    hermTraceNorm hA = 2 * s := by
  have key : ∀ i, (hA.eigenvalues i) ^ 2 = s * |hA.eigenvalues i| := by
    intro i
    have h := eigenvalues_cube hA hcube i
    set l := hA.eigenvalues i with hlv
    rcases eq_or_ne l 0 with h0 | h0
    · simp [h0]
    · have hsq : l ^ 2 = s ^ 2 := by field_simp at h; linarith [h]
      have habs : |l| = s := by
        have habs' : |l| = |s| := by rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs, hsq]
        rwa [abs_of_nonneg hs] at habs'
      rw [habs, hsq]; ring
  have hsum : ∑ i, (hA.eigenvalues i) ^ 2 = 2 * s ^ 2 := sum_sq_eigenvalues_eq hA htr
  have hmain : s * hermTraceNorm hA = 2 * s ^ 2 := by
    rw [hermTraceNorm, Finset.mul_sum, ← hsum]
    exact Finset.sum_congr rfl fun i _ => (key i).symm
  rcases eq_or_lt_of_le hs with h0 | h0
  · have hz : ∀ i, hA.eigenvalues i = 0 := by
      intro i
      have hk := key i
      rw [← h0] at hk
      exact pow_eq_zero_iff two_ne_zero |>.mp (by simpa using hk)
    simp [hermTraceNorm, hz, ← h0]
  · nlinarith [hmain, h0]

end Spectral

/-! ## The trace distance between two pure states -/

section Main

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For unit vectors `u`, `v` the overlap `‖⟪u,v⟫‖` is at most `1`.  (Proved here from the
trace identity `tr((P-Q)²) = 2(1 - ‖⟪u,v⟫‖²) = ∑ λᵢ² ≥ 0`.) -/
lemma one_sub_normSq_inn_nonneg {u v : n → ℂ} (hu : inn u u = 1) (hv : inn v v = 1) :
    0 ≤ 1 - ‖inn u v‖ ^ 2 := by
  have hH := projDiff_isHermitian u v
  have hsum := sum_sq_eigenvalues_eq hH (projDiff_trace_sq hu hv)
  have hnn : (0 : ℝ) ≤ ∑ i, (hH.eigenvalues i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hsum] at hnn
  linarith

/-- **Trace distance between two pure states.**  For unit vectors `u`, `v` in `ℂⁿ`, the trace
norm of the difference of the corresponding rank-one projections is `2√(1 - ‖⟪u,v⟫‖²)`. -/
theorem hermTraceNorm_projDiff {u v : n → ℂ} (hu : inn u u = 1) (hv : inn v v = 1) :
    hermTraceNorm (projDiff_isHermitian u v) = 2 * Real.sqrt (1 - ‖inn u v‖ ^ 2) := by
  set s := Real.sqrt (1 - ‖inn u v‖ ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 - ‖inn u v‖ ^ 2 :=
    Real.sq_sqrt (one_sub_normSq_inn_nonneg hu hv)
  refine hermTraceNorm_of_cube _ (Real.sqrt_nonneg _) ?_ ?_
  · rw [hs2]; exact projDiff_cube hu hv
  · rw [hs2]; exact projDiff_trace_sq hu hv

/-- **Cos Trace Norm 2003.**  If `u` and `v` are unit vectors in `ℂⁿ` and `θ ∈ [0, π/2]` is the
angle between the lines they span, i.e. `cos θ = ‖⟪u, v⟫‖`, then the trace norm of the
difference of the corresponding rank-one projections equals `2 sin θ`. -/
theorem CosTraceNorm2003 {u v : n → ℂ} (hu : inn u u = 1) (hv : inn v v = 1)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) (hcos : Real.cos θ = ‖inn u v‖) :
    hermTraceNorm (projDiff_isHermitian u v) = 2 * Real.sin θ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hsin : Real.sin θ = Real.sqrt (1 - ‖inn u v‖ ^ 2) := by
    rw [Real.sin_eq_sqrt_one_sub_cos_sq hθ0 (by linarith [Real.pi_pos]), hcos]
  rw [hsin]
  exact hermTraceNorm_projDiff hu hv

end Main

end Brockian

