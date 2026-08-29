import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a primitive root modulo the prime `p` if its residue generates the
multiplicative group `(ZMod p)ˣ`, i.e. it has multiplicative order `p - 1`. -/

theorem isPrimitiveRootMod_neg_one_three : IsPrimitiveRootMod (-1) 3 := by
  have h : orderOf ((-1 : ℤ) : ZMod 3) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  simpa [IsPrimitiveRootMod] using h

/-!
### Verified base cases

Concrete primes witnessing that the conjecture's conclusion does hold for small data.
-/

/-- `2` is a primitive root modulo `5`. -/
