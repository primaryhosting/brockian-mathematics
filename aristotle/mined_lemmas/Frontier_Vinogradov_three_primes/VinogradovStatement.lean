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

def VinogradovStatement : Prop :=
  ∃ N : Nat, ∀ n : Nat, N ≤ n → n % 2 = 1 → IsSumOfThreePrimes n

/-- The binary (strong) Goldbach conjecture: every even number `≥ 4` is a sum of two primes. -/
