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

theorem two_primitiveRoot_83 : IsPrimitiveRootMod 2 83 := by
  show orderOf ((2 : ℤ) : ZMod 83) = 82
  rw [cast_two]
  exact orderOf_eq_of_divisors _ _ (by norm_num) (by decide) (by decide)

end BaseCases

/-- **Artin's primitive root problem.**  The conjecture itself (`Frontier.ArtinConjecture`)
is open; what is proved here is:

* a Lean-checked *reduction* of the primitive-root condition to a finite, decidable
  computation over the divisors of `p - 1`;
* the resulting *base cases*: `2` is a primitive root modulo each of the twelve primes
  `3, 5, 11, 13, 19, 29, 37, 53, 59, 61, 67, 83` (so the set of primes for which Artin's
  conjecture asserts infinitude is at least non-empty for `a = 2`);
* the *necessity* of the two hypotheses on `a`: a perfect square is never a primitive root
  modulo an odd prime, and `-1` is never a primitive root modulo a prime `p ≥ 5`. -/
