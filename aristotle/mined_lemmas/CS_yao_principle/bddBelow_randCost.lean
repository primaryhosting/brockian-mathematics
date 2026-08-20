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

private lemma bddBelow_randCost (cost : A → X → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ A => randCost cost p) := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  set m : ℝ := Finset.univ.inf' (Finset.univ_nonempty) (fun z : A × X => cost z.1 z.2) with hm
  refine ⟨m, ?_⟩
  rintro r ⟨p, rfl⟩
  have hp0 : ∀ a, 0 ≤ (p : A → ℝ) a := p.2.1
  have hp1 : ∑ a, (p : A → ℝ) a = 1 := p.2.2
  have hbdd' : BddAbove (Set.range fun x : X => ∑ a, (p : A → ℝ) a * cost a x) :=
    Finite.bddAbove_range _
  have : m ≤ ∑ a, (p : A → ℝ) a * cost a x₀ := by
    calc m = ∑ a, (p : A → ℝ) a * m := by rw [← Finset.sum_mul, hp1, one_mul]
      _ ≤ ∑ a, (p : A → ℝ) a * cost a x₀ := by
          refine Finset.sum_le_sum fun a _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hp0 a)
          exact Finset.inf'_le (fun z : A × X => cost z.1 z.2) (Finset.mem_univ (a, x₀))
  exact le_trans this (le_ciSup hbdd' x₀)

