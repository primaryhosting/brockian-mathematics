/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

set_option maxRecDepth 100000

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue class generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is `p - 1`. -/

theorem two_primitiveRoot_5 : IsPrimitiveRootMod 2 5 := by
  show orderOf ((2 : ℤ) : ZMod 5) = 4
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

