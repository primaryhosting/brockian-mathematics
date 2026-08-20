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

def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  ∀ x : ZMod p, x ≠ 0 → ∃ n : ℕ, (a : ZMod p) ^ n = x

/-- The set of primes for which `a` is a primitive root. -/
