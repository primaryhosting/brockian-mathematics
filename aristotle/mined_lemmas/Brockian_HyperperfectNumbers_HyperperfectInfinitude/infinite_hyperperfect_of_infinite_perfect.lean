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

/-- `sigma1 n` is the sum of all divisors of `n`. -/

theorem infinite_hyperperfect_of_infinite_perfect (H : {n : ℕ | n.Perfect}.Infinite) :
    {n : ℕ | IsHyperperfect n}.Infinite := by
  refine H.mono ?_
  intro n hn
  exact ⟨1, (isKHyperperfect_one_iff_perfect hn.2).2 hn⟩

/-!
## Sample hyperperfect numbers

Unconditional verifications of small instances (including `28` and `325`, which lie outside the
family above).
-/

set_option maxRecDepth 40000 in
example : IsKHyperperfect 1 6 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 40000 in
example : IsKHyperperfect 2 21 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 40000 in
example : IsKHyperperfect 1 28 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
example : IsKHyperperfect 3 325 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
example : IsKHyperperfect 6 301 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
example : IsKHyperperfect 12 697 := ⟨by norm_num, by decide⟩

/-- `6` arises from the seed `m = 1`, `21` from `m = 2`, `301` from `m = 6`. -/
example : HyperperfectSeed 1 ∧ HyperperfectSeed 2 ∧ HyperperfectSeed 6 :=
  ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩⟩

end Brockian.HyperperfectNumbers

