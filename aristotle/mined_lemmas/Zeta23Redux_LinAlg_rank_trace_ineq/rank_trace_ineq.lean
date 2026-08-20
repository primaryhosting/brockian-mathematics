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

theorem rank_trace_ineq {r b : ℕ} {P Q : Matrix (Fin d) (Fin d) ℂ} (hP : P.PosSemidef)
    (hQ : Q.IsHermitian) (hr : P.rank ≤ r) (hb : posIndex hQ ≤ b) {c : ℝ} (hc : 0 < c) :
    c * rtrace P - (c ^ 2 / 4) * r + 2 * c * rtrace Q - c ^ 2 * b ≤ frobSq (P + Q) := by
  have hEh : (suppProj hP.isHermitian).IsHermitian := suppProj_isHermitian _
  have hEpsd : (suppProj hP.isHermitian).PosSemidef := suppProj_posSemidef _
  have hE1 : ((1 : Matrix (Fin d) (Fin d) ℂ) - suppProj hP.isHermitian).PosSemidef :=
    one_sub_suppProj_posSemidef _
  have hTh : (posProj hQ).IsHermitian := posProj_isHermitian hQ
  have hT2 : posProj hQ * posProj hQ = posProj hQ := posProj_mul_self hQ
  have hTpsd : (posProj hQ).PosSemidef := posProj_posSemidef hQ
  have hrb := r_bound hP hTh hT2
  have hpp := p_part hP (S := 1 - posProj hQ) (Matrix.isHermitian_one.sub hTh)
  set E := suppProj hP.isHermitian with hEdef
  set T := posProj hQ with hTdef
  set S : Matrix (Fin d) (Fin d) ℂ := 1 - T with hSdef
  have hSh : S.IsHermitian := Matrix.isHermitian_one.sub hTh
  have hSS : S * S = S := by
    rw [hSdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hT2]
    simp
  have hTS : T * S = 0 := by rw [hSdef, Matrix.mul_sub, hT2, Matrix.mul_one, sub_self]
  have hST : S * T = 0 := by rw [hSdef, Matrix.sub_mul, hT2, Matrix.one_mul, sub_self]
  set R := S * E * S with hRdef
  have hRh : R.IsHermitian := by
    show Rᴴ = R
    rw [hRdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh.eq, hEh.eq,
      Matrix.mul_assoc]
  have hRpsd : R.PosSemidef := by
    have h := hEpsd.conjTranspose_mul_mul_same S
    rwa [hSh.eq] at h
  have hR1 : ((1 : Matrix (Fin d) (Fin d) ℂ) - R).PosSemidef := by
    have h2 : (1 : Matrix (Fin d) (Fin d) ℂ) - R = T + S * (1 - E) * S := by
      have h3 : S * (1 - E) * S = S * S - S * E * S := by
        noncomm_ring
      rw [h3, hSS, ← hRdef, hSdef]
      abel
    rw [h2]
    refine hTpsd.add ?_
    have h := hE1.conjTranspose_mul_mul_same S
    rwa [hSh.eq] at h
  have hTR : T * R = 0 := by
    rw [hRdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTS, Matrix.zero_mul, Matrix.zero_mul]
  have hRT : R * T = 0 := by rw [hRdef, Matrix.mul_assoc, hST, Matrix.mul_zero]
  set B := ((c : ℝ) : ℂ) • T + ((c / 2 : ℝ) : ℂ) • R with hBdef
  have hBh : B.IsHermitian := by
    show Bᴴ = B
    rw [hBdef, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      hTh.eq, hRh.eq]
    simp
  have hAh : (P + Q).IsHermitian := hP.isHermitian.add hQ
  have key := two_rtrace_mul_sub_frobSq_le hAh hBh
  -- the Frobenius norm of the test matrix
  have hfB : frobSq B = c ^ 2 * rtrace T + (c ^ 2 / 4) * rtrace (R * R) := by
    rw [hBdef, frobSq_smul_add_smul hTh hRh hTR hRT, frobSq_eq_rtrace, frobSq_eq_rtrace,
      hTh.eq, hRh.eq, hT2]
    ring
  -- the linear term
  have hlin : rtrace ((P + Q) * B)
      = c * (rtrace (P * T) + rtrace (Q * T)) + (c / 2) * (rtrace (P * R) + rtrace (Q * R)) := by
    rw [hBdef, rtrace_mul_smul_add_smul, Matrix.add_mul, Matrix.add_mul, rtrace_add, rtrace_add]
  -- the two estimates
  have hPS : rtrace (P * S) = rtrace P - rtrace (P * T) := by
    rw [hSdef, Matrix.mul_sub, Matrix.mul_one, rtrace_sub]
  rw [hPS] at hpp
  have hq := q_part hQ hRpsd hR1 hRT
  rw [← hTdef] at hq
  have hEr : rtrace E ≤ (r : ℝ) := by
    rw [hEdef, rtrace_suppProj]
    exact_mod_cast hr
  have hTb : rtrace T ≤ (b : ℝ) := by
    rw [hTdef, rtrace_posProj]
    exact_mod_cast hb
  -- combine
  have hA1 : c * rtrace P ≤ c * (2 * rtrace (P * T) + rtrace (P * R)) := by nlinarith
  have hA2 : 2 * c * rtrace Q ≤ c * (2 * rtrace (Q * T) + rtrace (Q * R)) := by nlinarith
  have hA3 : c ^ 2 * rtrace T ≤ c ^ 2 * b := by nlinarith [sq_nonneg c]
  have hA4 : (c ^ 2 / 4) * rtrace (R * R) ≤ (c ^ 2 / 4) * r := by nlinarith [sq_nonneg c]
  linarith

/-- The specialization of `rank_trace_ineq` at `c = 2`. -/
