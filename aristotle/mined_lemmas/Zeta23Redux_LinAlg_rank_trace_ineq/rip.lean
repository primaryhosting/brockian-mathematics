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

noncomputable def rip (X Y : Matrix (Fin d) (Fin d) ℂ) : ℝ := (Matrix.trace (Xᴴ * Y)).re

/-- The number of strictly positive eigenvalues of a Hermitian matrix. -/
