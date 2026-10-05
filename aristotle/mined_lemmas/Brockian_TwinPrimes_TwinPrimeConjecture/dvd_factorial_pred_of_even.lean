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

/-
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Nat

namespace Brockian.TwinPrimes

/-- **The Twin Prime Conjecture**: there are arbitrarily large primes `p` such that
`p + 2` is also prime. -/

theorem dvd_factorial_pred_of_even {n : ℕ} (hev : 2 ∣ n) (hn : 6 ≤ n) : n ∣ (n - 1)! := by
  obtain ⟨k, rfl⟩ := hev
  have hk : 3 ≤ k := by omega
  have h1 : k * (2 * k - 2) ∣ (2 * k - 1)! :=
    mul_dvd_factorial_of_lt (by omega) (by omega) (le_refl _)
  refine dvd_trans ?_ h1
  refine ⟨k - 1, ?_⟩
  have h2 : 2 * k - 2 = 2 * (k - 1) := by omega
  rw [h2]
  ring

/-! ## Clement's criterion -/

/-- **Clement's theorem**: for `n > 1`, the pair `(n, n+2)` is a twin prime pair if and only if
`n * (n + 2)` divides `4 * ((n-1)! + 1) + n`. -/
