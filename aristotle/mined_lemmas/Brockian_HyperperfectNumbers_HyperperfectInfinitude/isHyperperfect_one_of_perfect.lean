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

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigma n` is the sum of all divisors of `n`. -/

lemma isHyperperfect_one_of_perfect {n : ℕ} (hn : Nat.Perfect n) (h1 : 1 < n) :
    IsHyperperfect 1 n := by
  have h : sigma n = 2 * n := by
    have := (Nat.perfect_iff_sum_divisors_eq_two_mul (by omega)).1 hn
    simpa [sigma] using this
  exact ⟨one_pos, h1, by omega⟩

/-! ## The `p, p² - p + 1` family

If `p` and `q = p² - p + 1` are both prime, then `p * q` is `(p-1)`-hyperperfect.
For `p = 2, 3, 7, 43, ...` this gives `6, 21, 301, ...`. -/

