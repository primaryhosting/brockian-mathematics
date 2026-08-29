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

/-- The primitive fifth root of unity used for the five-ray wheel. -/

theorem e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  simp only [e_eq_stdAddChar]
  exact AddChar.map_add_eq_mul ZMod.stdAddChar a b

/-- Consequence of `e_eq_stdAddChar`: `e 0 = 1`. -/
