import Mathlib
import RequestProject.Vinogradov

/-!
# Vinogradov three primes: Mathlib-phrased companion

`RequestProject/Vinogradov.lean` is import-free (its required header comment must be the
very first thing in the file, and Lean forbids `import` after any other command), so it
uses a self-contained trial-division primality predicate `Frontier.IsPrime` and encodes
oddness as `n % 2 = 1`.  Here we check that these agree with Mathlib's `Nat.Prime` and
`Odd`, and restate the results in Mathlib's vocabulary.
-/

namespace Frontier

/-- The trial-division predicate used in the import-free file agrees with `Nat.Prime`. -/

theorem infinite_odd_sums_of_three_primes :
    {n : ℕ | Odd n ∧ IsSumOfThreePrimes n}.Infinite := by
  apply Set.Infinite.mono (s := (fun p => p + 4) '' {p : ℕ | p.Prime ∧ Odd p})
  · rintro n ⟨p, ⟨hp, k, hk⟩, rfl⟩
    simp only [Set.mem_setOf_eq]
    refine ⟨⟨k + 2, by omega⟩, ?_⟩
    rw [isSumOfThreePrimes_iff]
    exact ⟨p, 2, 2, hp, Nat.prime_two, Nat.prime_two, by ring⟩
  · refine Set.Infinite.image (Set.injOn_of_injective fun a b h => by omega) ?_
    have hset : {p : ℕ | p.Prime ∧ Odd p} = {p : ℕ | p.Prime} \ {2} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hp, hodd⟩
        exact ⟨hp, by rintro rfl; simp [Nat.odd_iff] at hodd⟩
      · rintro ⟨hp, h2⟩
        exact ⟨hp, hp.odd_of_ne_two h2⟩
    rw [hset]
    exact Nat.infinite_setOf_prime.diff (Set.finite_singleton 2)

end Frontier

/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (Lean 4 core only), because Lean requires `import`
commands to precede every other command in a file, and the header above must be the first
thing in the file.  The companion file `RequestProject/VinogradovMathlib.lean` imports
Mathlib and proves that the primality and oddness predicates used here agree with
Mathlib's `Nat.Prime` and `Odd`, and restates the results in Mathlib's vocabulary.
-/

namespace Frontier

/-- Primality by trial division; agrees with Mathlib's `Nat.Prime`
(see `Frontier.isPrime_iff_nat_prime`). -/
