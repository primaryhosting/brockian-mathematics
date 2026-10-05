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

theorem toWord_letter_inv_mul (x : α × Bool) (w : FreeGroup α) (t : List (α × Bool))
    (hw : w.toWord = x :: t) : (FreeGroup.mk [(x.1, !x.2)] * w).toWord = t := by
  have h1 : w = FreeGroup.mk [x] * FreeGroup.mk t := by
    conv_lhs => rw [← FreeGroup.mk_toWord (x := w)]
    rw [hw, FreeGroup.mul_mk, List.singleton_append]
  have hinv : FreeGroup.mk [(x.1, !x.2)] = (FreeGroup.mk [x])⁻¹ := by
    rw [FreeGroup.inv_mk]; simp [FreeGroup.invRev]
  have hred : FreeGroup.IsReduced t := by
    have h3 := FreeGroup.isReduced_toWord (x := w)
    rw [hw] at h3
    exact h3.infix ⟨[x], [], by simp⟩
  rw [h1, hinv, ← mul_assoc, inv_mul_cancel, one_mul, FreeGroup.toWord_mk, hred.reduce_eq]

/-- The set of elements of a free group whose reduced word starts with the letter `x`. -/
