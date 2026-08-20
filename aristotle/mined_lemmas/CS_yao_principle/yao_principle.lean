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

theorem yao_principle (cost : A → X → ℝ) :
    (⨅ p : stdSimplex ℝ A, ⨆ x : X, ∑ a, (p : A → ℝ) a * cost a x) =
      ⨆ q : stdSimplex ℝ X, ⨅ a : A, ∑ x, (q : X → ℝ) x * cost a x := by
  show (⨅ p : stdSimplex ℝ A, randCost cost p) = ⨆ q : stdSimplex ℝ X, distCost cost q
  obtain ⟨q, hq, hqv, -⟩ := exists_hard_distribution cost
  refine le_antisymm ?_ ?_
  · rw [hqv]
    exact le_ciSup (bddAbove_distCost cost) (⟨q, hq⟩ : stdSimplex ℝ X)
  · exact ciSup_le fun q' => le_ciInf fun p => distCost_le_randCost cost p.2 q'.2

end Yao

end CS

