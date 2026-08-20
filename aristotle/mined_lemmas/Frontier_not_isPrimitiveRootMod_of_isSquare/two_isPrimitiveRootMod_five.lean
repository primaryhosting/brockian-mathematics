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

theorem two_isPrimitiveRootMod_five : IsPrimitiveRootMod 2 5 :=
  isPrimitiveRootMod_of_bounded (by decide)

/-- `2` is a primitive root modulo `13`. -/
