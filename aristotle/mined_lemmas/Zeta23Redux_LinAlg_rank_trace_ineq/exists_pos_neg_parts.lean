/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma exists_pos_neg_parts {Q : Matrix (Fin d) (Fin d) ℂ} (hQ : Q.IsHermitian) :
    ∃ Qp Qm : Matrix (Fin d) (Fin d) ℂ, Qp.PosSemidef ∧ Qm.PosSemidef ∧ Q = Qp - Qm ∧
      Qp * Qm = 0 ∧ ∀ c : ℝ, 2 * c * rtrace Qp ≤ frobSq Qp + c ^ 2 * (posIndex Q : ℝ) := by
  obtain ⟨U, hU1, hU2, hspec⟩ := exists_spectral hQ
  set mu : Fin d → ℝ := hQ.eigenvalues with hmu
  set fp : Fin d → ℝ := fun i => max (mu i) 0 with hfp
  set fm : Fin d → ℝ := fun i => max (-(mu i)) 0 with hfm
  refine ⟨U * diagonal (fun i => ((fp i : ℝ) : ℂ)) * Uᴴ,
    U * diagonal (fun i => ((fm i : ℝ) : ℂ)) * Uᴴ,
    conj_posSemidef (diagonal_posSemidef_of_nonneg (fun i => le_max_right _ _)),
    conj_posSemidef (diagonal_posSemidef_of_nonneg (fun i => le_max_right _ _)), ?_, ?_, ?_⟩
  · have hdiff : ∀ i, fp i - fm i = mu i := by
      intro i
      by_cases h : 0 ≤ mu i
      · simp [hfp, hfm, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
      · push_neg at h
        simp [hfp, hfm, max_eq_right h.le, max_eq_left (neg_nonneg.mpr h.le)]
    have hd : diagonal (fun i => ((mu i : ℝ) : ℂ))
        = diagonal (fun i => ((fp i : ℝ) : ℂ)) - diagonal (fun i => ((fm i : ℝ) : ℂ)) := by
      rw [Matrix.diagonal_sub]
      congr 1
      funext i
      rw [← Complex.ofReal_sub, hdiff]
    rw [hspec, hd, Matrix.mul_sub, Matrix.sub_mul]
  · rw [conj_mul hU1, Matrix.diagonal_mul_diagonal]
    have hz : (fun i => ((fp i : ℝ) : ℂ) * ((fm i : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul]
      by_cases h : 0 ≤ mu i
      · simp [hfm, max_eq_right (neg_nonpos.mpr h)]
      · push_neg at h
        simp [hfp, max_eq_right h.le]
    rw [hz]
    simp
  · intro c
    rw [conj_rtrace hU1, conj_frobSq hU1, rtrace_diagonal, frobSq_diagonal]
    have hpi : (posIndex Q : ℝ) = ∑ i, (if 0 < mu i then (1 : ℝ) else 0) := by
      rw [posIndex, dif_pos hQ, ← hmu]
      simp [Finset.sum_boole]
    rw [hpi, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases h : 0 < mu i
    · have hfpi : fp i = mu i := by simp [hfp, max_eq_left h.le]
      rw [hfpi, if_pos h]
      nlinarith [sq_nonneg (mu i - c)]
    · have hfpi : fp i = 0 := by simp [hfp, max_eq_right (not_lt.mp h)]
      rw [hfpi, if_neg h]
      simp

/-- The orthogonal projection onto the range of a positive semidefinite matrix. -/
