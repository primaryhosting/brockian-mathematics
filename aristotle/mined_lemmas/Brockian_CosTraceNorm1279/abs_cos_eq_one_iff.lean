/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian

/-- The planar rotation matrix by angle `θ`. -/

theorem abs_cos_eq_one_iff (x : ℝ) : |Real.cos x| = 1 ↔ Real.sin x = 0 := by
  constructor
  · intro h
    have h2 : Real.cos x ^ 2 = 1 := by
      have := congrArg (fun t : ℝ => t ^ 2) h
      simpa [sq_abs] using this
    have := Real.sin_sq_add_cos_sq x
    nlinarith [this, h2]
  · intro h
    have h2 : Real.cos x ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq x
      rw [h] at this
      nlinarith [this]
    have : |Real.cos x| ^ 2 = 1 := by simpa [sq_abs] using h2
    nlinarith [abs_nonneg (Real.cos x), this]

/--
**Cos Trace Norm 1279.**

For every angle `θ` and every exponent `n`, the `n`-th power of the planar rotation
`rot θ` is the rotation by `n * θ`, its trace equals `2 * cos (n * θ)`, this trace is
bounded in absolute value by `2`, and the bound is attained exactly when
`sin (n * θ) = 0`.  Moreover the bound is strict in the complementary case.
-/
