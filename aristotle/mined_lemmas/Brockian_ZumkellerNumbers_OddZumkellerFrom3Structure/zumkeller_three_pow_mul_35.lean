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

theorem zumkeller_three_pow_mul_35 {b : ℕ} (hb : 3 ≤ b) : IsZumkeller (3 ^ b * 35) := by
  obtain ⟨A, hA, hAsum⟩ := exists_subset_sum_shift b hb 0 (by norm_num) (by norm_num)
  refine ⟨by positivity, A, hA, ?_⟩
  have hcast : ((2 * ∑ d ∈ A, d : ℕ) : ℤ) = ((∑ d ∈ (3 ^ b * 35 : ℕ).divisors, d : ℕ) : ℤ) := by
    push_cast
    rw [hAsum]
    have hσ := sum_divisors_three_pow_mul_35 b
    push_cast at hσ
    rw [hσ]
    ring
  exact_mod_cast hcast

/-- **Odd Zumkeller numbers from 3-structure.**

For every exponent `a ≥ 3` and every odd `m` coprime to `105 = 3 * 5 * 7`, the number
`n = 3 ^ a * 35 * m = 3 ^ a * 5 * 7 * m` is an odd Zumkeller number whose `3`-part is exactly
`3 ^ a`.  In particular the three-structure `3 ^ a * 5 * 7` with `a ≥ 3` generates odd
Zumkeller numbers. -/
