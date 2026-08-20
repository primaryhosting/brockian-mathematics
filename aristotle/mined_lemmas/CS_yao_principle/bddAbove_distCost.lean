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

private lemma bddAbove_distCost (cost : A → X → ℝ) :
    BddAbove (Set.range fun q : stdSimplex ℝ X => distCost cost q) := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty A›
  set Mx : ℝ := Finset.univ.sup' (Finset.univ_nonempty) (fun z : A × X => cost z.1 z.2) with hMx
  refine ⟨Mx, ?_⟩
  rintro r ⟨q, rfl⟩
  have hq0 : ∀ x, 0 ≤ (q : X → ℝ) x := q.2.1
  have hq1 : ∑ x, (q : X → ℝ) x = 1 := q.2.2
  have hbdd : BddBelow (Set.range fun a : A => ∑ x, (q : X → ℝ) x * cost a x) :=
    Finite.bddBelow_range _
  have : ∑ x, (q : X → ℝ) x * cost a₀ x ≤ Mx := by
    calc ∑ x, (q : X → ℝ) x * cost a₀ x ≤ ∑ x, (q : X → ℝ) x * Mx := by
          refine Finset.sum_le_sum fun x _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hq0 x)
          exact Finset.le_sup' (fun z : A × X => cost z.1 z.2) (Finset.mem_univ (a₀, x))
      _ = Mx := by rw [← Finset.sum_mul, hq1, one_mul]
  exact le_trans (ciInf_le hbdd a₀) this

/-- **Existence of a hard input distribution.**  There is an input distribution `q` whose
distributional complexity equals the randomized complexity; in particular `q` certifies the
optimal lower bound for every randomized algorithm. -/
