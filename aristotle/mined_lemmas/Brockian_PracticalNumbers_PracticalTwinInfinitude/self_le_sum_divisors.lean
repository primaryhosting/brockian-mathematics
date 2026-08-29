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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian.PracticalNumbers

/-- A positive natural number `n` is *practical* when every `m ≤ n` can be written as a sum
of distinct divisors of `n`. -/

lemma self_le_sum_divisors {n : ℕ} (hn : 0 < n) : n ≤ ∑ y ∈ n.divisors, y :=
  Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i)
    (Nat.mem_divisors_self n hn.ne')

/-- Stewart's lemma: if `n` is practical and `1 ≤ d ≤ σ(n) + 1`, then `n * d` is practical. -/
