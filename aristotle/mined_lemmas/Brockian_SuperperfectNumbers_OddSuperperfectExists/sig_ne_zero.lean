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

namespace Brockian
namespace SuperperfectNumbers

open Finset

/-- The sum-of-divisors function `σ₁`. -/

lemma sig_ne_zero {n : ℕ} (hn : n ≠ 0) : sig n ≠ 0 := by
  have : 1 ≤ ∑ d ∈ n.divisors, d :=
    Finset.single_le_sum (f := fun d => d) (by intros; positivity) (Nat.one_mem_divisors.mpr hn)
  rw [sig_eq_sum]; omega

/-- Structure of an odd superperfect number: writing `σ(n) = 2 ^ a * k` with `k` odd,
one has `(2 ^ (a+1) - 1) * σ(k) = 2n`; in particular the Mersenne number `2 ^ (a+1) - 1`
divides `n`. -/
