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

theorem isPrime_iff_nat_prime (p : ℕ) : IsPrime p ↔ Nat.Prime p := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hm hmp hd => h m hmp hm (Nat.dvd_iff_mod_eq_zero.mp hd)⟩
  · rintro ⟨h2, h⟩
    exact ⟨h2, fun m hmp hm hmod => h m hm hmp (Nat.dvd_of_mod_eq_zero hmod)⟩

/-- `IsSumOfThreePrimes` says exactly what it should, in Mathlib's vocabulary. -/

theorem isSumOfThreePrimes_iff (n : ℕ) :
    IsSumOfThreePrimes n ↔ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n := by
  simp only [IsSumOfThreePrimes, isPrime_iff_nat_prime]

/-- Mathlib-phrased form of the target reduction: the binary Goldbach conjecture implies
that every sufficiently large odd number is a sum of three primes. -/

theorem Vinogradov_three_primes_mathlib
    (hG : ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n := by
  obtain ⟨N, hN⟩ := Vinogradov_three_primes fun n hn hodd => by
    obtain ⟨p, q, hp, hq, hpq⟩ := hG n hn (Nat.even_iff.mpr hodd)
    exact ⟨p, q, (isPrime_iff_nat_prime p).mpr hp, (isPrime_iff_nat_prime q).mpr hq, hpq⟩
  exact ⟨N, fun n hn hodd => (isSumOfThreePrimes_iff n).mp (hN n hn (Nat.odd_iff.mp hodd))⟩

/-- Mathlib-phrased form of the unconditional base case. -/

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → p % m ≠ 0

instance : DecidablePred IsPrime := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `n` is a sum of three primes. -/

def IsSumOfThreePrimes (n : Nat) : Prop :=
  ∃ p q r : Nat, IsPrime p ∧ IsPrime q ∧ IsPrime r ∧ p + q + r = n

/-- The Vinogradov ("ternary Goldbach") statement: every sufficiently large odd number is a
sum of three primes. -/

def VinogradovStatement : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → n % 2 = 1 → IsSumOfThreePrimes n

/-- The binary (strong) Goldbach conjecture: every even number `≥ 4` is a sum of two primes. -/

def GoldbachBinary : Prop :=
  ∀ n : Nat, 4 ≤ n → n % 2 = 0 → ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = n

theorem isPrime_three : IsPrime 3 := by decide

/-- **Lean-checked reduction (target).**  The binary Goldbach conjecture implies the
Vinogradov three-primes statement, with explicit threshold `N = 7`: for odd `n ≥ 7` write
`n = 3 + (n - 3)`, where `n - 3` is even and `≥ 4`, and split `n - 3` into two primes.

Mathlib contains no form of the ternary Goldbach theorem (there is no lemma about sums of
three primes, and `exact?`/`apply?` find nothing for the unconditional statement), so the
unconditional Vinogradov–Helfgott theorem cannot be cited here.  What is established is
this reduction, together with the unconditional base range `Vinogradov_base_case` below. -/

theorem Vinogradov_three_primes (hG : GoldbachBinary) : VinogradovStatement := by
  refine ⟨7, fun n hn hodd => ?_⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := hG (n - 3) (by omega) (by omega)
  exact ⟨p, q, 3, hp, hq, isPrime_three, by omega⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Unconditional base case, verified by kernel computation: every odd `n` with
`7 ≤ n < 500` is a sum of three primes. -/

theorem Vinogradov_base_case :
    ∀ n : Nat, n < 500 → 7 ≤ n → n % 2 = 1 → IsSumOfThreePrimes n := by
  have key : ∀ n < 500, 7 ≤ n → n % 2 = 1 →
      ∃ p < n, IsPrime p ∧ IsPrime (n - 3 - p) ∧ p + (n - 3 - p) + 3 = n := by decide
  intro n hn h7 hodd
  obtain ⟨p, -, hp, hq, hsum⟩ := key n hn h7 hodd
  exact ⟨p, n - 3 - p, 3, hp, hq, isPrime_three, hsum⟩

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
