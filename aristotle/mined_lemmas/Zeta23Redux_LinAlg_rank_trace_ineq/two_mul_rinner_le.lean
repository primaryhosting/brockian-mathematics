/-
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Lean requires `import` to precede any module docstring, so the header is
repeated as a module docstring immediately after the import below.)
-/
import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped ComplexOrder

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

open Matrix

/-- Square complex matrices of size `Fin d`. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

variable {d : ℕ}

/-- The real part of the trace. -/

lemma two_mul_rinner_le {M N : Mat d} (hM : M.IsHermitian) (hN : N.IsHermitian) (t : ℝ) :
    2 * t * rinner M N ≤ frobSq M + t ^ 2 * frobSq N := by
  have hS := smul_isHermitian hN t
  have h0 := frobSq_nonneg (M - (t : ℂ) • N)
  rw [frobSq_eq_rinner (hM.sub hS)] at h0
  simp only [rinner_sub_left, rinner_sub_right, rinner_smul_right,
    rinner_comm ((t : ℂ) • N) M, rinner_comm ((t : ℂ) • N) N] at h0
  rw [frobSq_eq_rinner hM, frobSq_eq_rinner hN]
  nlinarith [h0]

/-- The trace pairing of a positive semidefinite matrix with a square of a Hermitian
matrix is nonnegative. -/
