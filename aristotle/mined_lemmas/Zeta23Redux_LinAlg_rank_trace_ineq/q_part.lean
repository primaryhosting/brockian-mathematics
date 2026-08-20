/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Proof outline

Write `E` for the orthogonal projection onto the range of `P` (so `tr E = rank P`), `Π` for the
spectral projection of `Q` onto its positive eigenvalues (so `tr Π = posIndex Q`), `S = 1 - Π`
and `R = S E S`.  Testing the Hermitian matrix `A = P + Q` against the Hermitian matrix
`B = c Π + (c/2) R` via `0 ≤ ‖A - B‖_F²` gives `2 tr (A B) - ‖B‖_F² ≤ ‖A‖_F²`.  Since `Π R = 0`,
`‖B‖_F² = c² tr Π + (c²/4) tr (R²)`, and `tr (R²) ≤ tr E` because
`E S E - (E S E)² = ((1 - E) S E)ᴴ ((1 - E) S E)` is positive semidefinite.  The linear term
splits into a `P`-part, `2 tr (P Π) + tr (P R) ≥ tr P`, which is exactly
`0 ≤ tr ((1 - E S E) P (1 - E S E))`, and a `Q`-part, `2 tr (Q Π) + tr (Q R) ≥ 2 tr Q`, which is
checked eigenvalue by eigenvalue using `0 ≤ R ≤ 1` and `R Π = 0`.
-/

namespace Zeta23Redux.LinAlg

open Matrix Finset
open scoped ComplexOrder

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma q_part {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) {R : Matrix (Fin d) (Fin d) ℂ}
    (hR : R.PosSemidef) (hR1 : (1 - R).PosSemidef) (hRP : R * posProj hQ = 0) :
    2 * rtrace Q ≤ 2 * rtrace (Q * posProj hQ) + rtrace (Q * R) := by
  classical
  set U : Matrix (Fin d) (Fin d) ℂ := (hQ.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set W : Matrix (Fin d) (Fin d) ℂ := star U * R * U with hW
  have hUs : star U = Uᴴ := rfl
  have hUU : star U * U = 1 := star_mul_u hQ
  have hWpsd : W.PosSemidef := by rw [hW, hUs]; exact hR.conjTranspose_mul_mul_same U
  have hW1 : ((1 : Matrix (Fin d) (Fin d) ℂ) - W).PosSemidef := by
    have h := hR1.conjTranspose_mul_mul_same U
    rw [← hUs, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUU, ← hW] at h
    exact h
  have hd0 : ∀ i, 0 ≤ (W i i).re := fun i => by
    simpa using (Complex.le_def.mp (hWpsd.diag_nonneg (i := i))).1
  have hd1 : ∀ i, (W i i).re ≤ 1 := fun i => by
    have h := (Complex.le_def.mp (hW1.diag_nonneg (i := i))).1
    simp [Matrix.sub_apply, Matrix.one_apply_eq] at h
    linarith
  set D : Matrix (Fin d) (Fin d) ℂ :=
    diagonal (fun i => if 0 < hQ.eigenvalues i then (1 : ℂ) else 0) with hD
  have hWD : W * D = 0 := by
    have h : star U * (R * posProj hQ) * U = W * D := by
      rw [posProj, sfc, ← hU, ← hD]
      rw [show star U * (R * (U * D * star U)) * U = (star U * R * U) * D * (star U * U) by
        noncomm_ring, hUU, Matrix.mul_one, ← hW]
    rw [hRP] at h
    simpa using h.symm
  have hzero : ∀ i, 0 < hQ.eigenvalues i → W i i = 0 := by
    intro i hi
    have h := congrFun (congrFun hWD i) i
    rw [hD, Matrix.mul_diagonal] at h
    simpa [hi] using h
  have htQ : rtrace Q = ∑ i, hQ.eigenvalues i := by
    rw [rtrace, hQ.trace_eq_sum_eigenvalues, Complex.re_sum]
    simp
  have htQP : rtrace (Q * posProj hQ)
      = ∑ i, (if 0 < hQ.eigenvalues i then hQ.eigenvalues i else 0) := by
    have h1 := sfc_mul hQ (fun x => (x : ℂ)) (fun x => if 0 < x then 1 else 0)
    rw [sfc_self hQ] at h1
    rw [rtrace, posProj, h1, sfc_trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 0 < hQ.eigenvalues i <;> simp [h]
  have htQR : rtrace (Q * R) = ∑ i, hQ.eigenvalues i * (W i i).re := by
    have h1 : (Q * R).trace = (diagonal (fun i => ((hQ.eigenvalues i : ℝ) : ℂ)) * W).trace := by
      conv_lhs => rw [← sfc_self hQ]
      rw [sfc, ← hU, Matrix.trace_mul_comm]
      rw [show R * (U * diagonal (fun i => ((hQ.eigenvalues i : ℝ) : ℂ)) * star U)
          = (R * U) * (diagonal (fun i => ((hQ.eigenvalues i : ℝ) : ℂ)) * star U) by noncomm_ring]
      rw [Matrix.trace_mul_comm]
      congr 1
      rw [hW]
      noncomm_ring
    rw [rtrace, h1,
      show (diagonal (fun i => ((hQ.eigenvalues i : ℝ) : ℂ)) * W).trace
        = ∑ i, ((hQ.eigenvalues i : ℝ) : ℂ) * W i i by
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq],
      Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by simp
  rw [htQ, htQP, htQR, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases h : 0 < hQ.eigenvalues i
  · simp [h, hzero i h]
  · push_neg at h
    have h0 := hd0 i
    have h1 := hd1 i
    simp only [if_neg (not_lt.mpr h), mul_zero, zero_add]
    nlinarith

/-- The abstract Frobenius norm bound: for Hermitian idempotents `E` and `T`,
`tr (((1-T) E (1-T))²) ≤ tr E`. -/
