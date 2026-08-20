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

lemma rip_comm (X Y : Matrix (Fin d) (Fin d) ℂ) : rip X Y = rip Y X := by
  unfold rip
  rw [show (Yᴴ * X) = (Xᴴ * Y)ᴴ from by simp, Matrix.trace_conjTranspose]
  simp

