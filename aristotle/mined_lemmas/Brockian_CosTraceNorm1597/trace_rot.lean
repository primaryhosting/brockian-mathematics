import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian

open Matrix

/-- The planar rotation matrix by angle `θ`. -/

lemma trace_rot (θ : ℝ) : (rot θ).trace = 2 * Real.cos θ := by
  simp [rot, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]
  ring

/--
**Cos Trace Norm 1597.**

For every angle `θ`, the planar rotation matrix `rot θ` is orthogonal, its trace equals
`2 cos θ`, and this trace is bounded in absolute value by its trace norm, namely the
dimension `2`; equality holds exactly when `cos θ = ±1`.
-/
