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

def artinPrimes (a : ℤ) : Set ℕ := {p | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots** (qualitative form): for every integer `a`
which is neither `-1` nor a perfect square, `a` is a primitive root modulo infinitely
many primes. -/
