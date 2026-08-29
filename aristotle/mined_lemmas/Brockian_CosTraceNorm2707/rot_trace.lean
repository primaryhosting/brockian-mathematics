/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain comment because Lean requires `import` to precede any
-- module docstring; the identical header is repeated as the module docstring below.)

import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix
open scoped MatrixOrder

namespace Brockian

/-- The trace norm (Schatten 1-norm) of a complex square matrix `A`:
the trace of the positive semidefinite square root of `Aᴴ * A`,
i.e. the sum of the singular values of `A`. -/

theorem rot_trace (θ : ℝ) : (rot θ).trace = 2 * (Real.cos θ : ℂ) := by
  simp [rot, Matrix.trace, Fin.sum_univ_succ]
  ring

/--
**Cos Trace Norm 2707.**
For every angle `θ`, the `2 × 2` rotation matrix `R(θ)` has trace norm `2`,
its trace has norm `2 |cos θ|`, and consequently the trace-norm bound
`|tr R(θ)| ≤ ‖R(θ)‖₁` holds, i.e. `2 |cos θ| ≤ 2`.
-/
