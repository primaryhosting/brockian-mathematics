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

theorem infinitude_primes_4k3 (N : ℕ) : ∃ p, N < p ∧ Nat.Prime p ∧ p % 4 = 3 := by
  obtain ⟨F, hF1, hFdvd⟩ : ∃ F : ℕ, 1 ≤ F ∧ ∀ p : ℕ, Nat.Prime p → p ≤ N → p ∣ F :=
    ⟨Nat.factorial N, Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _),
      fun p hp hpN => Nat.dvd_factorial hp.pos hpN⟩
  have hnmod : (4 * F - 1) % 4 = 3 := by omega
  obtain ⟨p, hp, hpd, hpmod⟩ := exists_prime_factor_mod_four_eq_three _ hnmod
  refine ⟨p, ?_, hp, hpmod⟩
  by_contra hle
  push_neg at hle
  have h4 : p ∣ 4 * F := (hFdvd p hp hle).mul_left 4
  have h1 : p ∣ 1 := by
    have h := Nat.dvd_sub h4 hpd
    rwa [Nat.sub_sub_self (by omega : 1 ≤ 4 * F)] at h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- The same statement obtained instead from Mathlib's theorem on primes in arithmetic
progressions, `Nat.forall_exists_prime_gt_and_modEq` (Dirichlet). -/
