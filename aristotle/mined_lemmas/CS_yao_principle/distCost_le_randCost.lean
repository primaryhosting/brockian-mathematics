/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Overview

Mathlib has no minimax theorem, so the result is proved from scratch.  The only nontrivial
input from Mathlib is the separation theorem `geometric_hahn_banach_compact_closed`
(`Mathlib/Analysis/LocallyConvex/Separation.lean`), which is used to prove Ville's theorem of
the alternative (`CS.ville_alternative`).  Yao's principle then follows by applying the
alternative to the shifted cost matrix `cost a x - v`, where `v` is the randomized complexity,
together with weak duality (`CS.distCost_le_randCost`).
-/

namespace CS

section Orthant

variable {A : Type*}

/-- The nonnegative orthant in `A → ℝ` is convex. -/

theorem distCost_le_randCost (cost : A → X → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A)
    {q : X → ℝ} (hq : q ∈ stdSimplex ℝ X) : distCost cost q ≤ randCost cost p := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have hbdd : BddBelow (Set.range fun a : A => ∑ x, q x * cost a x) :=
    Finite.bddBelow_range _
  have hbdd' : BddAbove (Set.range fun x : X => ∑ a, p a * cost a x) :=
    Finite.bddAbove_range _
  have h1 : distCost cost q ≤ ∑ a, p a * (∑ x, q x * cost a x) := by
    calc distCost cost q = ∑ a, p a * distCost cost q := by
            rw [← Finset.sum_mul, hp1, one_mul]
      _ ≤ ∑ a, p a * (∑ x, q x * cost a x) := by
            refine Finset.sum_le_sum fun a _ => ?_
            exact mul_le_mul_of_nonneg_left (ciInf_le hbdd a) (hp0 a)
  have h2 : ∑ x, q x * (∑ a, p a * cost a x) ≤ randCost cost p := by
    calc ∑ x, q x * (∑ a, p a * cost a x)
        ≤ ∑ x, q x * randCost cost p := by
          refine Finset.sum_le_sum fun x _ => ?_
          exact mul_le_mul_of_nonneg_left (le_ciSup hbdd' x) (hq0 x)
      _ = randCost cost p := by rw [← Finset.sum_mul, hq1, one_mul]
  have hswap : ∑ a, p a * (∑ x, q x * cost a x) = ∑ x, q x * (∑ a, p a * cost a x) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring
  linarith [h1, h2, hswap.le, hswap.ge]

