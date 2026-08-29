/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not permit a module doc-comment `/-! ... -/` before `import`,
-- so the required header appears above as an ordinary block comment.)

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-! ## Elementary trigonometric estimates -/

/-- A crude but explicit linear lower bound for `sin` on `[0, 5π/8]`. -/

theorem E_shift (t : ℝ) (n : ℤ) : E (t + 2 * Real.pi * n) = E t := by
  rw [E_add, E_int_two_pi, mul_one]

/-! ## The Shor measurement distribution

The first register is prepared in the uniform superposition over `x < Q`, the oracle writes
`f x` in the second register, and the quantum Fourier transform of order `Q` is applied to the
first register.  `amp Q f c y` is the resulting amplitude of the basis state `|c⟩|y⟩` and
`prob Q f c` is the probability that measuring the first register yields `c`. -/

/-- Amplitude of `|c⟩ ⊗ |y⟩` after the quantum Fourier transform in Shor's algorithm. -/
