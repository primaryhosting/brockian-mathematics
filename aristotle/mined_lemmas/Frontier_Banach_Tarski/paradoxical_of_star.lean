/-
/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (Lean requires `import` to be the first command, so the header above is wrapped
-- in a block comment; it is repeated verbatim as the module docstring below.)
import Mathlib

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
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

set_option grind.warning false

/-!
## Overview

We develop the general theory of equidecomposability and paradoxical decompositions
for a group action, following the classical route to the Banach–Tarski paradox:

* `Frontier.Equidecomposable G A B` : `A` and `B` are `G`-equidecomposable (Mathlib's
  `Equidecomp` structure is used as the underlying notion of a finite piecewise-`G` bijection).
* `Frontier.Paradoxical G E` : `E` contains two disjoint subsets, each `G`-equidecomposable
  with `E` itself.

Main results proved here:

* `Frontier.paradoxical_freeGroup` : the free group of rank two is paradoxical
  (acting on itself by left translation).  This is the combinatorial *base case* of
  Banach–Tarski.
* `Frontier.paradoxical_of_freeAction` : any set carrying a free action of the rank two
  free group is paradoxical.  (Hausdorff-type transfer principle, uses choice.)
* `Frontier.Banach_Tarski` : the Lean-checked geometric reduction: if the unit sphere in
  `ℝ³` is paradoxical under rotations, then the closed unit ball is paradoxical under
  isometries.
-/

namespace Frontier

open Metric Set Function

/-! ### Equidecomposability and paradoxical decompositions -/

/-- `A` and `B` are `G`-equidecomposable: there is a bijection from `A` to `B` obtained by
splitting `A` into finitely many pieces and applying a single element of `G` to each piece. -/

theorem paradoxical_of_star {Y : Type*} [MulAction F2 Y] (E : Set Y) (star : Set F2 → Set Y)
    (h_union : ∀ S T, star (S ∪ T) = star S ∪ star T)
    (h_disj : ∀ S T, Disjoint S T → Disjoint (star S) (star T))
    (h_smul : ∀ (g : F2) (S : Set F2), g • star S = star (g • S))
    (h_univ : star Set.univ = E)
    (h_sub : ∀ S, star S ⊆ E) :
    Paradoxical F2 E := by
  refine ⟨star (wA ∪ wA'), star (wB ∪ wB'), h_sub _, h_sub _, ?_, ?_, ?_⟩
  · refine h_disj _ _ ?_
    simp only [Set.disjoint_union_left, Set.disjoint_union_right]
    exact ⟨⟨disjoint_startingWith (by decide), disjoint_startingWith (by decide)⟩,
      disjoint_startingWith (by decide), disjoint_startingWith (by decide)⟩
  · refine equidecomposable_two_piece (star wA) (star wA') 1 genA
      (h_disj _ _ (disjoint_startingWith (by decide))) ?_ (h_union _ _).symm ?_
    · rw [one_smul, h_smul, smul_wA']
      exact h_disj _ _ disjoint_compl_right
    · rw [one_smul, h_smul, smul_wA', ← h_union, Set.union_compl_self, h_univ]
  · refine equidecomposable_two_piece (star wB) (star wB') 1 genB
      (h_disj _ _ (disjoint_startingWith (by decide))) ?_ (h_union _ _).symm ?_
    · rw [one_smul, h_smul, smul_wB']
      exact h_disj _ _ disjoint_compl_right
    · rw [one_smul, h_smul, smul_wB', ← h_union, Set.union_compl_self, h_univ]

/-- **The base case of the Banach–Tarski paradox**: the free group of rank two admits a
paradoxical decomposition for its action on itself by left translation. -/
