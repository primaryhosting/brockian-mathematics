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

lemma key_proj {X R : Matrix (Fin d) (Fin d) ℂ} (hX : X.IsHermitian) (hR : R.IsHermitian)
    (hidem : R * R = R) (t : ℝ) :
    2 * t * rtrace (X * R) ≤ frobSq X + t ^ 2 * rtrace R := by
  set Y : Matrix (Fin d) (Fin d) ℂ := ((-t : ℝ) : ℂ) • R with hY
  have hst : Yᴴ = ((-t : ℝ) : ℂ) • R := by
    rw [hY, Matrix.conjTranspose_smul, hR.eq]; simp
  have hYh : Y.IsHermitian := by rw [Matrix.IsHermitian, hst, hY]
  have h0 : 0 ≤ frobSq (X + Y) := frobSq_nonneg _
  rw [frobSq_add_herm hX hYh] at h0
  have h1 : rtrace (X * Y) = -t * rtrace (X * R) := by
    rw [hY, rtrace, rtrace, Matrix.mul_smul, Matrix.trace_smul]
    simp
  have h2 : frobSq Y = t ^ 2 * rtrace R := by
    have hq : Yᴴ * Y = ((t ^ 2 : ℝ) : ℂ) • R := by
      rw [hst, hY, Matrix.smul_mul, Matrix.mul_smul, hidem, smul_smul]
      push_cast
      ring_nf
    rw [frobSq, hq, Matrix.trace_smul, rtrace, smul_eq_mul, Complex.re_ofReal_mul]
  rw [h1, h2] at h0
  linarith

/-! ### Conjugation by a unitary -/

