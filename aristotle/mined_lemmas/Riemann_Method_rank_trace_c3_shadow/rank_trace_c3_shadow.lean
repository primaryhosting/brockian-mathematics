/-
# Rank Trace C 3 Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Method.rank_trace_c3_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rank Trace C 3 Shadow
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Method.rank_trace_c3_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Method

/-- The `c = 3` scalar shadow of the rank-trace inequality: for all real `x`,
`3 * x - 9 / 4 ≤ x ^ 2`, equivalently `(x - 3 / 2) ^ 2 ≥ 0`.

The proof is the `sq_nonneg` shadow: `(x - 3/2)^2 ≥ 0` rearranges to the claim. -/

theorem rank_trace_c3_shadow (x : ℝ) : 3 * x - 9 / 4 ≤ x ^ 2 := by
  nlinarith [sq_nonneg (x - 3 / 2)]

/-- Equivalent square form of the `c = 3` shadow. -/
