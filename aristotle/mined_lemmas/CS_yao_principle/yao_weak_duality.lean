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

lemma yao_weak_duality {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]
    (cost : A → I → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) {q : I → ℝ}
    (hq : q ∈ stdSimplex ℝ I) :
    (⨅ a : A, ∑ i, q i * cost a i) ≤ ⨆ i : I, ∑ a, p a * cost a i := by
  have key : ∑ a, p a * (∑ i, q i * cost a i) = ∑ i, q i * (∑ a, p a * cost a i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  calc (⨅ a : A, ∑ i, q i * cost a i)
      ≤ ∑ a, p a * (∑ i, q i * cost a i) := ciInf_le_expectation hp _
    _ = ∑ i, q i * (∑ a, p a * cost a i) := key
    _ ≤ ⨆ i : I, ∑ a, p a * cost a i := expectation_le_ciSup hq _

/-- A continuous linear functional on `A → ℝ` (with `A` finite) is given by a vector. -/
