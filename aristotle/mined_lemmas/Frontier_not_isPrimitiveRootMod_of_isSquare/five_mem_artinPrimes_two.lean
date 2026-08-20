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

theorem five_mem_artinPrimes_two : 5 ∈ artinPrimes 2 :=
  ⟨by norm_num, two_isPrimitiveRootMod_five⟩

/-- **A Lean-checked reduction for Artin's conjecture**: the two exceptional hypotheses in
Artin's conjecture are exactly the right ones, i.e. they are *necessary*. If `a` is a
primitive root modulo infinitely many primes, then `a ≠ -1` and `a` is not a perfect
square. Consequently `ArtinConjecture` is, for each `a`, a statement about precisely the
integers for which infinitude is not excluded. -/
