import Mathlib

/-!
# E Eq Std Add Char
Category: Characters
Target: Brockian.Characters5.e_eq_stdAddChar
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Brockian
namespace Characters5

/-- The primitive fifth root of unity `ω = exp(2πi/5)`. -/

theorem e_eq_exp (k : ZMod 5) :
    e k = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / 5) := by
  rw [e, omega, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- The bespoke character equals Mathlib's standard additive character mod 5. -/
