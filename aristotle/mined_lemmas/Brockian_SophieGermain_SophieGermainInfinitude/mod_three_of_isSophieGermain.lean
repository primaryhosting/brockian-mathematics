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

-- # Sophie Germain Infinitude
-- Category: Brockian Conjecture
-- Target: Brockian.SophieGermain.SophieGermainInfinitude
-- Verification: pending
-- Provenance: Aristotle theorem prover (Harmonic)

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem mod_three_of_isSophieGermain {p : ℕ} (hp : IsSophieGermain p) (h2 : p ≠ 3)
    (h3 : 2 * p + 1 ≠ 3) : p % 3 = 2 := by
  have hp3 : ¬ (3 ∣ p) := fun h => h2 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp.1).mp h).symm
  have hq3 : ¬ (3 ∣ 2 * p + 1) := fun h =>
    h3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp.2).mp h).symm
  have h : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  interval_cases hm : (p % 3)
  · exact absurd (Nat.dvd_of_mod_eq_zero hm) hp3
  · exact absurd (by omega : (3 : ℕ) ∣ 2 * p + 1) hq3
  · rfl

/-! ## Sophie Germain's theorem on Mersenne numbers -/

