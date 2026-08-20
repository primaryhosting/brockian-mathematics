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

