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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect if `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one plus `k` times the
sum of its proper divisors other than `1`.  The definition is stated in the subtraction-free
form `k * σ n + 1 = (k + 1) * n + k`. -/

theorem isKHyperperfect_one_iff_perfect {n : ℕ} (hn : 1 < n) :
    IsKHyperperfect 1 n ↔ Nat.Perfect n := by
  have h0 : 0 < n := lt_trans one_pos hn
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul h0, IsKHyperperfect, sigma_one_apply]
  constructor
  · rintro ⟨-, -, h⟩; omega
  · intro h; exact ⟨one_pos, hn, by omega⟩

/-- Geometric sum identity over `ℕ`, in subtraction-free form. -/
