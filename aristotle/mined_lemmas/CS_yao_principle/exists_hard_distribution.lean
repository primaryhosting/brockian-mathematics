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

theorem exists_hard_distribution (cost : A → X → ℝ) :
    ∃ q ∈ stdSimplex ℝ X,
      (⨅ p : stdSimplex ℝ A, randCost cost p) = distCost cost q ∧
        ∀ p ∈ stdSimplex ℝ A, distCost cost q ≤ randCost cost p := by
  classical
  set v : ℝ := ⨅ p : stdSimplex ℝ A, randCost cost p
  have hbddI := bddBelow_randCost cost
  rcases ville_alternative (A := A) (X := X) (fun a x => cost a x - v) with ⟨p, hp, hpx⟩ | h
  · exfalso
    have hstrict : ∀ x, ∑ a, p a * cost a x < v := by
      intro x
      have hx := hpx x
      have hrw : ∑ a, p a * (cost a x - v) = (∑ a, p a * cost a x) - v := by
        simp only [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]
      linarith [hrw ▸ hx]
    have hlt : randCost cost p < v := ciSup_lt_of_forall_lt hstrict
    have hge : v ≤ randCost cost p := ciInf_le hbddI (⟨p, hp⟩ : stdSimplex ℝ A)
    exact absurd hge (not_le.2 hlt)
  · obtain ⟨q, hq, hqa⟩ := h
    have hall : ∀ a, v ≤ ∑ x, q x * cost a x := by
      intro a
      have ha := hqa a
      have hrw : ∑ x, q x * (cost a x - v) = (∑ x, q x * cost a x) - v := by
        simp only [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul]
      linarith [hrw ▸ ha]
    have h1 : v ≤ distCost cost q := le_ciInf hall
    have h2 : ∀ p ∈ stdSimplex ℝ A, distCost cost q ≤ randCost cost p :=
      fun p hp => distCost_le_randCost cost hp hq
    refine ⟨q, hq, le_antisymm h1 ?_, h2⟩
    exact le_ciInf fun p => h2 p p.2

/-- **Yao's minimax principle**.  For a finite set `A` of deterministic algorithms, a finite
set `X` of inputs and a cost matrix `cost`, the optimal worst-case expected cost of a
randomized algorithm (a distribution over `A`) equals the optimal, over input distributions,
of the best deterministic algorithm's expected cost. -/
