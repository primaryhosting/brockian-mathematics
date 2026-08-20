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

theorem hasDerivAt_bhEntropy (k hbar c G M : ℝ) :
    HasDerivAt (bhEntropy k hbar c G) (8 * Real.pi * k * G * M / (hbar * c)) M := by
  have h : HasDerivAt (fun M : ℝ => M ^ 2) (2 * M) M := by
    simpa using (hasDerivAt_pow 2 M)
  have hfun : bhEntropy k hbar c G = fun x : ℝ => (4 * Real.pi * k * G) * x ^ 2 / (hbar * c) := by
    funext x; simp [bhEntropy]
  rw [hfun]
  have h' := (h.const_mul (4 * Real.pi * k * G)).div_const (hbar * c)
  convert h' using 1
  ring

/-- The derivative of the black-hole entropy with respect to mass. -/
