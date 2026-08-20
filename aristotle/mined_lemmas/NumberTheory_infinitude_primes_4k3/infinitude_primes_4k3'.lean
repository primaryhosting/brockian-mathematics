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

theorem infinitude_primes_4k3' (N : ℕ) : ∃ p, N < p ∧ Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 4) (a := 3) (by norm_num) (by decide)
  exact ⟨p, hpN, hp, by simpa [Nat.ModEq] using hmod⟩

/-- Equivalent phrasing: the set of primes congruent to `3` mod `4` is infinite. -/
