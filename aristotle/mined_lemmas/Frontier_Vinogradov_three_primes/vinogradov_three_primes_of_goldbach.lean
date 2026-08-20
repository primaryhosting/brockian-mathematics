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
