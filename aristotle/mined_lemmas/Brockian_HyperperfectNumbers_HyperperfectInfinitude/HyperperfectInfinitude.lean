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

/-- The sum of all divisors of `n`, i.e. `σ₁ n`. -/

theorem HyperperfectInfinitude
    (h : {p : ℕ | p.Prime ∧ (partner p).Prime}.Infinite) :
    {n : ℕ | IsHyperperfect n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun a => ?_)
  obtain ⟨p, ⟨hp, hq⟩, hpa⟩ := h.exists_gt a
  refine ⟨p * partner p, isHyperperfect_partner hp hq, ?_⟩
  have h1 : 1 ≤ partner p := by simp [partner]
  calc a < p := hpa
    _ ≤ p * partner p := Nat.le_mul_of_pos_right p h1

end Brockian.HyperperfectNumbers

