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
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Superperfect Exists
Category: Brockian Conjecture
Target: Brockian.SuperperfectNumbers.OddSuperperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *superperfect* when `σ(σ(n)) = 2n`. Whether an odd superperfect
number exists is an open problem, so the target result
`Brockian.SuperperfectNumbers.OddSuperperfectExists` is a Lean-checked *conditional
reduction*: the existence of an odd superperfect number is equivalent to the existence of
one satisfying a list of proved necessary conditions (size lower bound from a kernel
computation, deficiency bounds, non-divisibility by `3` in the non-square case, and parity
information in the square case).
-/

namespace Brockian.SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ(n) = ∑_{d ∣ n} d`. -/

theorem not_three_dvd_of_even_sigma {n : ℕ} (hodd : Odd n) (h : Superperfect n)
    (he : Even (sigma n)) : ¬ (3 ∣ n) := by
  rintro ⟨k, hk⟩
  have hn : 1 < n := h.one_lt
  have hbound := sigma_bound_of_even_sigma h he
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- `n = 3` (`k = 0` and `k = 1` are excluded by `1 < n`)
    interval_cases k
    · omega
    · -- n = 3, σ(3) = 4, σ(4) = 7 ≠ 6
      have h3 : n = 3 := by omega
      subst h3
      have : sigma 3 = 4 := by decide
      have h4 : sigma (sigma 3) = 7 := by rw [this]; decide
      have := h.2
      omega
  · have := add_add_one_le_sigma (N := n) (a := 3) (b := k) hk (by norm_num) hk2
    omega

/-- The parity of a sum of odd numbers is the parity of the number of summands. -/
