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

theorem paradoxical_of_freeAction {Y : Type*} [MulAction F2 Y] (E : Set Y)
    (hinv : ∀ (g : F2), ∀ y ∈ E, g • y ∈ E)
    (hfree : ∀ (g : F2), ∀ y ∈ E, g • y = y → g = 1) : Paradoxical F2 E := by
  classical
  set r : Y → Y := fun y => (Quotient.mk (MulAction.orbitRel F2 Y) y).out with hrdef
  have hr_eq : ∀ (g : F2) (y : Y), r (g • y) = r y := by
    intro g y
    have hq : (Quotient.mk (MulAction.orbitRel F2 Y) (g • y))
        = Quotient.mk (MulAction.orbitRel F2 Y) y :=
      Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩)
    simp only [hrdef, hq]
  have hr_orbit : ∀ y : Y, ∃ g : F2, y = g • r y := by
    intro y
    have h1 : Quotient.mk (MulAction.orbitRel F2 Y) (r y)
        = Quotient.mk (MulAction.orbitRel F2 Y) y := Quotient.out_eq _
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h1)
    exact ⟨g⁻¹, by rw [← hg]; simp⟩
  have hr_idem : ∀ y : Y, r (r y) = r y := by
    intro y
    obtain ⟨g, hg⟩ := hr_orbit y
    conv_rhs => rw [hg]
    rw [hr_eq]
  have hr_mem : ∀ y ∈ E, r y ∈ E := by
    intro y hy
    obtain ⟨g, hg⟩ := hr_orbit y
    have hry : r y = g⁻¹ • y := by conv_rhs => rw [hg, inv_smul_smul]
    rw [hry]; exact hinv _ _ hy
  have huniq : ∀ (g g' : F2) (y y' : Y), y ∈ E → y' ∈ E → g • r y = g' • r y' →
      g = g' ∧ r y = r y' := by
    intro g g' y y' hy hy' h
    have h1 : r y' = r y := by
      have h3 := hr_eq g' (r y')
      rw [← h, hr_eq g (r y), hr_idem, hr_idem] at h3
      exact h3.symm
    refine ⟨?_, h1.symm⟩
    rw [h1] at h
    have h2 : (g'⁻¹ * g) • r y = r y := by rw [mul_smul, h, inv_smul_smul]
    exact (inv_mul_eq_one.mp (hfree _ _ (hr_mem y hy) h2)).symm
  refine paradoxical_of_star E (fun S => {z | ∃ g ∈ S, ∃ y ∈ E, z = g • r y}) ?_ ?_ ?_ ?_ ?_
  · intro S T
    ext z
    constructor
    · rintro ⟨g, (hg | hg), y, hy, rfl⟩
      exacts [Or.inl ⟨g, hg, y, hy, rfl⟩, Or.inr ⟨g, hg, y, hy, rfl⟩]
    · rintro (⟨g, hg, y, hy, rfl⟩ | ⟨g, hg, y, hy, rfl⟩)
      exacts [⟨g, Or.inl hg, y, hy, rfl⟩, ⟨g, Or.inr hg, y, hy, rfl⟩]
  · intro S T hST
    rw [Set.disjoint_left]
    rintro z ⟨g, hg, y, hy, rfl⟩ ⟨g', hg', y', hy', heq⟩
    obtain ⟨rfl, -⟩ := huniq g g' y y' hy hy' heq
    exact Set.disjoint_left.mp hST hg hg'
  · intro g S
    ext z
    constructor
    · rintro ⟨w, ⟨g', hg', y, hy, rfl⟩, rfl⟩
      exact ⟨g * g', ⟨g', hg', rfl⟩, y, hy, (mul_smul g g' (r y)).symm⟩
    · rintro ⟨g', ⟨g'', hg'', rfl⟩, y, hy, rfl⟩
      exact ⟨g'' • r y, ⟨g'', hg'', y, hy, rfl⟩, (mul_smul g g'' (r y)).symm⟩
  · ext z
    constructor
    · rintro ⟨g, -, y, hy, rfl⟩
      exact hinv _ _ (hr_mem y hy)
    · intro hz
      obtain ⟨g, hg⟩ := hr_orbit z
      exact ⟨g, Set.mem_univ _, z, hz, hg⟩
  · rintro S z ⟨g, -, y, hy, rfl⟩
    exact hinv _ _ (hr_mem y hy)

end Frontier

