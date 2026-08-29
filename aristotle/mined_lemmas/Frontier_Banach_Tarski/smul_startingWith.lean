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

theorem smul_startingWith (x : α × Bool) :
    (FreeGroup.mk [x] : FreeGroup α) • startingWith (x.1, !x.2) = (startingWith x)ᶜ := by
  have hx : ((x.1, !x.2).1, !(x.1, !x.2).2) = x := by simp
  ext u
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' : w.toWord.head? = some (x.1, !x.2) := hw
    obtain ⟨t, ht⟩ : ∃ t, w.toWord = (x.1, !x.2) :: t := by
      cases hL : w.toWord with
      | nil => rw [hL] at hw'; simp at hw'
      | cons hd tl =>
          rw [hL] at hw'; simp only [List.head?_cons, Option.some.injEq] at hw'
          exact ⟨tl, by rw [hw']⟩
    have hkey := toWord_letter_inv_mul (x.1, !x.2) w t ht
    rw [hx] at hkey
    intro hc
    have hcc : (FreeGroup.mk [x] * w).toWord.head? = some x := hc
    rw [hkey] at hcc
    have hred := FreeGroup.isReduced_toWord (x := w)
    rw [ht] at hred
    cases hT : t with
    | nil => rw [hT] at hcc; simp at hcc
    | cons hd tl =>
        rw [hT] at hcc hred
        simp only [List.head?_cons, Option.some.injEq] at hcc
        rw [FreeGroup.isReduced_cons_cons] at hred
        have h1 := hred.1
        obtain ⟨a, b⟩ := hd
        subst hcc
        simp at h1
  · intro hu
    have hu' : u.toWord.head? ≠ some x := hu
    refine ⟨FreeGroup.mk [(x.1, !x.2)] * u, ?_, ?_⟩
    · show (FreeGroup.mk [(x.1, !x.2)] * u).toWord.head? = some (x.1, !x.2)
      rw [toWord_letter_mul (x.1, !x.2) u (by rw [hx]; exact hu')]
      simp
    · show FreeGroup.mk [x] * (FreeGroup.mk [(x.1, !x.2)] * u) = u
      have hinv : (FreeGroup.mk [(x.1, !x.2)] : FreeGroup α) = (FreeGroup.mk [x])⁻¹ := by
        rw [FreeGroup.inv_mk]; simp [FreeGroup.invRev]
      rw [hinv, ← mul_assoc, mul_inv_cancel, one_mul]

end FreeGroup

/-- Abbreviation for the free group of rank two. -/
abbrev F2 : Type := FreeGroup (Fin 2)

/-- The four sets of words starting with a given generator or its inverse. -/
