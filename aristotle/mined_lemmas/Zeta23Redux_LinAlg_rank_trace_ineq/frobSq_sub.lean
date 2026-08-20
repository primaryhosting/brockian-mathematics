import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ComplexOrder

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma frobSq_sub (X Y : Matrix (Fin d) (Fin d) ℂ) :
    frobSq (X - Y) = frobSq X - 2 * rip X Y + frobSq Y := by
  have h := rip_comm X Y
  unfold frobSq rip at *
  simp only [Matrix.conjTranspose_sub, sub_mul, mul_sub, Matrix.trace_sub, Complex.sub_re]
  linarith

