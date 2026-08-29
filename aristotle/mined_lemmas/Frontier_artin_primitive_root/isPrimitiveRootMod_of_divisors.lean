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

theorem isPrimitiveRootMod_of_divisors (a : ℤ) (p : ℕ) (hp : 0 < p - 1)
    (h1 : (a : ZMod p) ^ (p - 1) = 1)
    (h2 : ∀ q ∈ (p - 1).divisors, q.Prime → (a : ZMod p) ^ ((p - 1) / q) ≠ 1) :
    IsPrimitiveRootMod a p :=
  orderOf_eq_of_divisors _ _ hp h1 h2

/-- A perfect square is never a primitive root modulo an odd prime: this shows that the
hypothesis `¬ IsSquare a` in Artin's conjecture cannot be dropped. -/
