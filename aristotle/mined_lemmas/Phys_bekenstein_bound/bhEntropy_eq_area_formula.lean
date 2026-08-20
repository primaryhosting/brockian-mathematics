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

theorem bhEntropy_eq_area_formula {k hbar c G M : ℝ} (hc : c ≠ 0) (hG : G ≠ 0) :
    bhEntropy k hbar c G M = k * horizonArea G c M * c ^ 3 / (4 * G * hbar) := by
  unfold bhEntropy horizonArea schwarzschildRadius
  field_simp
  ring

/-- A Schwarzschild black hole saturates the Bekenstein bound: its entropy equals
`2 π k R E / (ℏ c)` for `R` its Schwarzschild radius and `E = M c ^ 2` its energy. -/
