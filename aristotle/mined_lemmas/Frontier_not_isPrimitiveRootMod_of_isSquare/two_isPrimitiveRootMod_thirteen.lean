/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` if every nonzero residue class mod `p`
is a power of `a`, i.e. `a` generates the multiplicative group `(ZMod p)ˣ`. -/

theorem two_isPrimitiveRootMod_thirteen : IsPrimitiveRootMod 2 13 :=
  isPrimitiveRootMod_of_bounded (by decide)

/-- The set of primes witnessing Artin's conjecture for `a = 2` is nonempty. -/
