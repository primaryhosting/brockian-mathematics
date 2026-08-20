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

lemma rip_smul (X A : Matrix (Fin d) (Fin d) ℂ) (t : ℝ) :
    rip X ((t : ℂ) • A) = t * rip X A := by
  unfold rip
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp

