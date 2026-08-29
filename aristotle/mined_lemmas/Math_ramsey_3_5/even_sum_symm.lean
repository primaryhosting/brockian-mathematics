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
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 5
Category: Pure Mathematics
Target: Math.ramsey_3_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph

namespace Math

/-! ## The Ramsey property -/

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s`, or an independent set of size `t` (a clique of size `t` in the complement).
Equivalently, every 2-colouring of the edges of `K n` has a red `K s` or a blue `K t`. -/

lemma even_sum_symm (f : V → V → ℕ) (hs : ∀ x y, f x y = f y x) (hd : ∀ x, f x x = 0)
    (A : Finset V) : Even (∑ v ∈ A, ∑ u ∈ A, f v u) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
      rw [Finset.sum_insert ha]
      have h1 : ∑ u ∈ insert a A, f a u = ∑ u ∈ A, f a u := by
        rw [Finset.sum_insert ha, hd a, zero_add]
      have h2 : ∀ v ∈ A, ∑ u ∈ insert a A, f v u = f v a + ∑ u ∈ A, f v u := by
        intro v _
        rw [Finset.sum_insert ha]
      rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
      have h3 : ∑ v ∈ A, f v a = ∑ u ∈ A, f a u := by
        exact Finset.sum_congr rfl (fun v _ => hs v a)
      rw [h3]
      have : ∑ u ∈ A, f a u + (∑ u ∈ A, f a u + ∑ v ∈ A, ∑ u ∈ A, f v u)
          = 2 * (∑ u ∈ A, f a u) + ∑ v ∈ A, ∑ u ∈ A, f v u := by ring
      rw [this]
      exact (even_two_mul _).add ih

variable {G : SimpleGraph V} [DecidableRel G.Adj]

