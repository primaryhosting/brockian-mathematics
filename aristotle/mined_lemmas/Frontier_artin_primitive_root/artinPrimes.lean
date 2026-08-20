import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

def artinPrimes (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots**: every integer `a` which is neither `-1`
nor a perfect square is a primitive root modulo infinitely many primes. -/
