/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- The standard simplex over a nonempty finite type is nonempty (it contains point masses). -/
instance nonempty_stdSimplex {X : Type*} [Fintype X] [Nonempty X] :
    Nonempty (stdSimplex ℝ X) :=
  ⟨⟨fun x => if Classical.arbitrary X = x then 1 else 0,
    ite_eq_mem_stdSimplex ℝ (Classical.arbitrary X)⟩⟩

/-- The expectation of `f` under a probability distribution is at least its minimum. -/

lemma expectation_le_ciSup {X : Type*} [Fintype X] [Nonempty X] {p : X → ℝ}
    (hp : p ∈ stdSimplex ℝ X) (f : X → ℝ) : (∑ x, p x * f x) ≤ ⨆ x, f x := by
  have hb : BddAbove (Set.range f) := Finite.bddAbove_range f
  calc (∑ x, p x * f x) ≤ ∑ x, p x * (⨆ x, f x) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (le_ciSup hb x) (hp.1 x)
    _ = ⨆ x, f x := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- Weak duality (the "easy" direction of Yao's principle): for any randomized algorithm
`p` and any input distribution `q`, the expected cost of the best deterministic algorithm
against `q` is at most the worst-case expected cost of `p`. -/
