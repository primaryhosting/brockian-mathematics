/-
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
Statement: State the Bekenstein bound S ≤ 2πkRE/ℏc.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Note: Lean 4 requires `import` to be the first command in a file, so this header is written as a
plain block comment `/- ... -/` rather than a module docstring `/-! ... -/`; the text is otherwise
exactly as specified.
-/

import Mathlib

open scoped Real

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Phys

/-- The Bekenstein bound `2 π k R E / (ℏ c)` on the entropy of a system of energy `E`
contained in a sphere of radius `R`. -/

noncomputable def bekensteinBound (k hbar c R E : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Schwarzschild radius `2 G M / c ^ 2` of a body of mass `M`. -/
