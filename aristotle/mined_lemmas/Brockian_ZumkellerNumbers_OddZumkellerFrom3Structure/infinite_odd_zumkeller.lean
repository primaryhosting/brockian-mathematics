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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.ZumkellerNumbers

/-- A positive integer `n` is a *Zumkeller number* if its set of divisors can be split into
two parts with equal sums, i.e. there is a set `A` of divisors of `n` whose sum is exactly
half of `σ(n)`. -/

theorem infinite_odd_zumkeller : {n : ℕ | Odd n ∧ IsZumkeller n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  refine ⟨3 ^ 3 * 35 * 11 ^ N, ?_, ?_⟩
  · obtain ⟨h1, h2, -, -⟩ := OddZumkellerFrom3Structure 3 (11 ^ N) le_rfl
      (Odd.pow (by decide)) (Nat.Coprime.pow_right _ (by decide))
    exact ⟨h1, h2⟩
  · have hlt : N < 11 ^ N := Nat.lt_pow_self (by norm_num)
    nlinarith [pow_pos (show 0 < 11 by norm_num) N]

/-!
## Necessary conditions: the shape of an odd Zumkeller number

The family produced above uses the three smallest odd primes `3, 5, 7`.  This is optimal:
an odd Zumkeller number is never a prime power or a product of two prime powers.
-/

/-- A Zumkeller number is abundant or perfect: `σ(n) ≥ 2 * n`. -/
