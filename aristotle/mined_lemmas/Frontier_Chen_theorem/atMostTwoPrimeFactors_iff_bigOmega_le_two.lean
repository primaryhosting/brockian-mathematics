/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `AtMostTwoPrimeFactors q` says that `q` is a product of at most two primes,
i.e. `q = 1`, or `q` is prime, or `q` is a product of two (not necessarily distinct)
primes.  Equivalently (see `atMostTwoPrimeFactors_iff_bigOmega_le_two`), the number of
prime factors of `q`, counted with multiplicity, is at most `2`.  These are the
"almost primes" `P₂` appearing in Chen's theorem. -/

theorem atMostTwoPrimeFactors_iff_bigOmega_le_two {q : ℕ} (hq : q ≠ 0) :
    AtMostTwoPrimeFactors q ↔ q.primeFactorsList.length ≤ 2 := by
  constructor
  · rintro (rfl | hp | ⟨a, b, ha, hb, rfl⟩)
    · simp
    · simp [Nat.primeFactorsList_prime hp]
    · have := Nat.perm_primeFactorsList_mul ha.ne_zero hb.ne_zero
      have hlen := this.length_eq
      simp [hlen, Nat.primeFactorsList_prime ha, Nat.primeFactorsList_prime hb]
  · intro hlen
    have hprod : q.primeFactorsList.prod = q := Nat.prod_primeFactorsList hq
    have hmem : ∀ p ∈ q.primeFactorsList, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactorsList hp
    match h : q.primeFactorsList with
    | [] => left; rw [← hprod, h]; simp
    | [a] =>
      right; left
      have : a.Prime := hmem a (by rw [h]; simp)
      rwa [← hprod, h, List.prod_singleton]
    | [a, b] =>
      right; right
      refine ⟨a, b, hmem a (by rw [h]; simp), hmem b (by rw [h]; simp), ?_⟩
      rw [← hprod, h]
      simp
    | a :: b :: c :: t => rw [h] at hlen; simp at hlen; omega

/-! ### Base case: an unconditional verification for small even numbers -/

/-- Every even number `n` with `4 ≤ n ≤ 60` admits a Chen representation (indeed a
representation as a sum of two primes). -/
