/-
# Norm E
Category: Characters
Target: Brockian.Characters5.norm_e
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

namespace Brockian.Characters5

/-- A primitive 5th root of unity `ω = exp(2πi/5)`. -/

noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e k = ω ^ k`. -/

noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- `ω` has unit modulus, since the exponent `2πi/5` is purely imaginary
(`Complex.norm_exp : ‖exp z‖ = Real.exp z.re`). -/
