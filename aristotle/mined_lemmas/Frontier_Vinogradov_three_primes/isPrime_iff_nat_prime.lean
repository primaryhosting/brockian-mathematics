import Mathlib
import RequestProject.Main

/-!
# Bridge to Mathlib's `Nat.Prime`

`RequestProject.Main` is import-free (so that the required header comment can be the very first
thing in the file, which Lean forbids for files containing `import` commands).  This file checks
that the elementary primality predicate `Frontier.IsPrime` used there is exactly Mathlib's
`Nat.Prime`, and restates the results of `RequestProject.Main` in Mathlib's vocabulary.
-/

namespace Frontier

/-- The elementary primality predicate used in `RequestProject.Main` agrees with Mathlib's
`Nat.Prime`. -/

theorem isPrime_iff_nat_prime (p : ℕ) : IsPrime p ↔ Nat.Prime p := by
  rw [Nat.prime_def_lt]
  constructor
  · rintro ⟨hp2, h⟩
    refine ⟨hp2, fun m hm hdvd => ?_⟩
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (by omega)
      · rfl
    · exact absurd (Nat.dvd_iff_mod_eq_zero.mp hdvd) (h m hm hm2)
  · rintro ⟨hp2, h⟩
    refine ⟨hp2, fun m hm hm2 hmod => ?_⟩
    have hdvd : m ∣ p := Nat.dvd_iff_mod_eq_zero.mpr hmod
    have := h m hm hdvd
    omega

/-- `Frontier.IsSumOfThreePrimes n` says exactly that `n` is a sum of three Mathlib-primes. -/
