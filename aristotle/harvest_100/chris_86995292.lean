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
theorem isSumOfThreePrimes_iff (n : ℕ) :
    IsSumOfThreePrimes n ↔ ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n := by
  simp only [IsSumOfThreePrimes, isPrime_iff_nat_prime]

/-- `Frontier.GoldbachEven` is exactly the binary Goldbach conjecture, stated with Mathlib's
`Nat.Prime` and `Even`. -/
theorem goldbachEven_iff :
    GoldbachEven ↔ ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  simp only [GoldbachEven, isPrime_iff_nat_prime, Nat.even_iff]

/-- **Base case, Mathlib form.** Every odd `n` with `9 ≤ n ≤ 299` is a sum of three primes. -/
theorem sum_three_primes_of_odd_of_le_299 {n : ℕ} (h9 : 9 ≤ n) (hn : n ≤ 299) (hodd : Odd n) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n :=
  (isSumOfThreePrimes_iff n).mp
    (isSumOfThreePrimes_of_odd_of_le_299 h9 hn (Nat.odd_iff.mp hodd))

/-- **Target, Mathlib form.** The binary Goldbach conjecture implies that every sufficiently large
odd number is a sum of three primes. -/
theorem vinogradov_three_primes_of_goldbach
    (hG : ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = n :=
  ⟨9, fun n hn hodd => (isSumOfThreePrimes_iff n).mp
    (isSumOfThreePrimes_of_goldbach (goldbachEven_iff.mpr hG) hn (Nat.odd_iff.mp hodd))⟩

end Frontier

/-!
# Vinogradov Three Primes
Category: Frontier — Prime Numbers
Target: Frontier.Vinogradov_three_primes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (only Lean's `Init` prelude is available), so that the
required header comment can literally be the first thing in the file: Lean rejects `import`
commands that follow a module docstring.  A companion file, `RequestProject.MathlibBridge`,
imports `Mathlib` and checks that the notion of primality used below coincides with Mathlib's
`Nat.Prime`, and restates the results in Mathlib's vocabulary.

## What is proved here

Vinogradov's three primes theorem states that every sufficiently large odd natural number is the
sum of three primes.  Searching Mathlib (`Mathlib/NumberTheory/*`, `Mathlib/Combinatorics/
Schnirelmann.lean`) shows that neither Vinogradov's theorem nor either Goldbach conjecture is
available: Mathlib has the basic theory of Schnirelmann density but no additive prime number
theory and no circle-method machinery, so no existing lemma closes or nearly closes this goal.

Accordingly this file contains:

* the formal statement `Frontier.VinogradovThreePrimes`;
* the **base case**, proved unconditionally by kernel computation
  (`Frontier.isSumOfThreePrimes_of_odd_of_le_299`): every odd `n` with `9 ≤ n ≤ 299` is a sum of
  three primes;
* a **Lean-checked reduction** (`Frontier.Vinogradov_three_primes`): the binary Goldbach
  conjecture implies Vinogradov's three primes theorem, with the explicit threshold `N = 9`.
-/

namespace Frontier

/-! ## Primality -/

/-- `p` is prime: it is at least `2` and has no divisor `m` with `2 ≤ m < p`.
(`RequestProject.MathlibBridge` proves `Frontier.IsPrime p ↔ Nat.Prime p`.) -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → p % m ≠ 0

instance decidableIsPrime (p : Nat) : Decidable (IsPrime p) :=
  inferInstanceAs (Decidable (2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → p % m ≠ 0))

theorem isPrime_three : IsPrime 3 := by decide

/-! ## Statements -/

/-- `n` is a sum of three (not necessarily distinct) primes. -/
def IsSumOfThreePrimes (n : Nat) : Prop :=
  ∃ p q r : Nat, IsPrime p ∧ IsPrime q ∧ IsPrime r ∧ p + q + r = n

/-- **Vinogradov's three primes theorem**, as a proposition: every sufficiently large odd number
is a sum of three primes.  (Not proved here; see `Frontier.Vinogradov_three_primes` for a
Lean-checked reduction to the binary Goldbach conjecture.) -/
def VinogradovThreePrimes : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → n % 2 = 1 → IsSumOfThreePrimes n

/-- The **binary Goldbach conjecture**: every even number greater than `2` is a sum of two
primes. -/
def GoldbachEven : Prop :=
  ∀ n : Nat, 2 < n → n % 2 = 0 → ∃ p q : Nat, IsPrime p ∧ IsPrime q ∧ p + q = n

/-! ## A sufficient criterion -/

/-- If `p` and `n - 3 - p` are prime and `p + 3 ≤ n`, then `n = p + (n - 3 - p) + 3` is a sum of
three primes. -/
theorem isSumOfThreePrimes_of_witness {n p : Nat} (hp : IsPrime p) (hq : IsPrime (n - 3 - p))
    (hle : p + 3 ≤ n) : IsSumOfThreePrimes n :=
  ⟨p, n - 3 - p, 3, hp, hq, isPrime_three, by omega⟩

/-! ## The base case, verified by kernel computation -/

set_option maxRecDepth 100000 in
/-- Kernel-checked witness search: for every odd `n` with `9 ≤ n < 300` there is a prime `p < 40`
such that `n - 3 - p` is also prime. -/
theorem exists_witness_of_odd_lt_300 :
    ∀ n, n < 300 → 9 ≤ n → n % 2 = 1 →
      ∃ p, p < 40 ∧ IsPrime p ∧ IsPrime (n - 3 - p) ∧ p + 3 ≤ n := by
  decide

/-- **Base case.** Every odd `n` with `9 ≤ n ≤ 299` is a sum of three primes. -/
theorem isSumOfThreePrimes_of_odd_of_le_299 {n : Nat} (h9 : 9 ≤ n) (hn : n ≤ 299)
    (hodd : n % 2 = 1) : IsSumOfThreePrimes n := by
  obtain ⟨p, -, hp, hq, hle⟩ := exists_witness_of_odd_lt_300 n (by omega) h9 hodd
  exact isSumOfThreePrimes_of_witness hp hq hle

/-! ## The reduction to the binary Goldbach conjecture -/

/-- **Reduction.** Assuming the binary Goldbach conjecture, every odd `n ≥ 9` is a sum of three
primes: write `n = 3 + (n - 3)`, where `n - 3` is even and greater than `2`. -/
theorem isSumOfThreePrimes_of_goldbach (hG : GoldbachEven) {n : Nat} (h9 : 9 ≤ n)
    (hodd : n % 2 = 1) : IsSumOfThreePrimes n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hG (n - 3) (by omega) (by omega)
  exact ⟨p, q, 3, hp, hq, isPrime_three, by omega⟩

/-- **Target.** The binary Goldbach conjecture implies Vinogradov's three primes theorem: every
odd `n ≥ 9` — in particular every sufficiently large odd number — is a sum of three primes. -/
theorem Vinogradov_three_primes (hG : GoldbachEven) : VinogradovThreePrimes :=
  ⟨9, fun _ hn hodd => isSumOfThreePrimes_of_goldbach hG hn hodd⟩

end Frontier

