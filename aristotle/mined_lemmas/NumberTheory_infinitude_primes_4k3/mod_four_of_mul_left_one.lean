/-
# Infinitude Primes 4 K 3
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.infinitude_primes_4k3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace NumberTheory

/-! ### An elementary Euclid-style argument

Every natural number congruent to `3` mod `4` has a prime factor congruent to `3` mod `4`,
because a product of numbers congruent to `1` mod `4` is again congruent to `1` mod `4`.
Applying this to `4 * N ! - 1` produces a prime `> N` congruent to `3` mod `4`. -/

/-- If `q ≡ 1 [MOD 4]` and `q * m ≡ 3 [MOD 4]`, then `m ≡ 3 [MOD 4]`. -/

private theorem mod_four_of_mul_left_one {q m : ℕ} (h1 : q % 4 = 1) (h3 : q * m % 4 = 3) :
    m % 4 = 3 := by
  rwa [Nat.mul_mod, h1, one_mul, Nat.mod_mod] at h3

/-- Any `n` with `n % 4 = 3` admits a prime divisor `p` with `p % 4 = 3`. -/
