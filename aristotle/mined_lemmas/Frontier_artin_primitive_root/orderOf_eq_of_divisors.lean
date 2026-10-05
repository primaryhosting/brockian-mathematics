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

theorem orderOf_eq_of_divisors {M : Type*} [Monoid M] (x : M) (n : ℕ) (hn : 0 < n)
    (h1 : x ^ n = 1) (h2 : ∀ q ∈ n.divisors, q.Prime → x ^ (n / q) ≠ 1) :
    orderOf x = n :=
  orderOf_eq_of_pow_and_pow_div_prime hn h1
    (fun q hq hd => h2 q (Nat.mem_divisors.mpr ⟨hd, hn.ne'⟩) hq)

/-- The primitive-root property is detected by a finite computation. -/
