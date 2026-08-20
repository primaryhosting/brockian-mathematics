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

lemma clm_apply_eq_sum {A : Type*} [Fintype A] [DecidableEq A] (f : (A → ℝ) →L[ℝ] ℝ)
    (x : A → ℝ) : f x = ∑ a, x a * f (Pi.single a 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : Pi.single a (x a) = x a • (Pi.single a (1:ℝ) : A → ℝ) := by
    ext b; by_cases hb : a = b <;> simp [Pi.single_apply, hb]
  rw [h, map_smul]
  simp

/-- **Key lemma** (a theorem of the alternative, the combinatorial core of the minimax
theorem): for any real payoff matrix `M`, either the column player has a distribution `q`
making every row expectation strictly positive, or the row player has a distribution `p`
making every column expectation nonpositive.

The proof separates the compact convex set of achievable payoff vectors from the open
positive orthant by a hyperplane (geometric Hahn–Banach). -/
