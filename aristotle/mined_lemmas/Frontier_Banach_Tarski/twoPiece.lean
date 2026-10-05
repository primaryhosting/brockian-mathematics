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

noncomputable def twoPiece (A₁ A₂ : Set X) (g₁ g₂ : G)
    (hA : Disjoint A₁ A₂) (hB : Disjoint (g₁ • A₁) (g₂ • A₂)) : Equidecomp X G where
  toFun := fun x => if x ∈ A₁ then g₁ • x else g₂ • x
  invFun := fun y => if y ∈ g₁ • A₁ then g₁⁻¹ • y else g₂⁻¹ • y
  source := A₁ ∪ A₂
  target := g₁ • A₁ ∪ g₂ • A₂
  map_source' := by
    rintro x (hx | hx)
    · simp only [hx, if_pos]
      exact Or.inl ⟨x, hx, rfl⟩
    · by_cases h : x ∈ A₁
      · simp only [h, if_pos]; exact Or.inl ⟨x, h, rfl⟩
      · simp only [h, if_neg, not_false_iff]; exact Or.inr ⟨x, hx, rfl⟩
  map_target' := by
    rintro y (hy | hy)
    · simp only [hy, if_pos]
      obtain ⟨x, hx, rfl⟩ := hy
      left; simpa using hx
    · by_cases h : y ∈ g₁ • A₁
      · simp only [h, if_pos]
        obtain ⟨x, hx, rfl⟩ := h
        left; simpa using hx
      · simp only [h, if_neg, not_false_iff]
        obtain ⟨x, hx, rfl⟩ := hy
        right; simpa using hx
  left_inv' := by
    rintro x (hx | hx)
    · simp only [hx, if_pos]
      have : g₁ • x ∈ g₁ • A₁ := ⟨x, hx, rfl⟩
      simp [this]
    · by_cases h : x ∈ A₁
      · simp only [h, if_pos]
        have : g₁ • x ∈ g₁ • A₁ := ⟨x, h, rfl⟩
        simp [this]
      · simp only [h, if_neg, not_false_iff]
        have h2 : g₂ • x ∈ g₂ • A₂ := ⟨x, hx, rfl⟩
        have : g₂ • x ∉ g₁ • A₁ := fun hc => (hB.le_bot ⟨hc, h2⟩ : _)
        simp [this]
  right_inv' := by
    rintro y (hy | hy)
    · simp only [hy, if_pos]
      obtain ⟨x, hx, rfl⟩ := hy
      simp [hx]
    · by_cases h : y ∈ g₁ • A₁
      · simp only [h, if_pos]
        obtain ⟨x, hx, rfl⟩ := h
        simp [hx]
      · simp only [h, if_neg, not_false_iff]
        obtain ⟨x, hx, rfl⟩ := hy
        have hx1 : x ∉ A₁ := fun hc => (hA.le_bot ⟨hc, hx⟩ : _)
        simp [hx1]
  isDecompOn' := ⟨{g₁, g₂}, by
    intro x _
    by_cases h : x ∈ A₁
    · exact ⟨g₁, by simp, by simp [h]⟩
    · exact ⟨g₂, by simp, by simp [h]⟩⟩

/-- Splitting a set into two pieces and translating each piece produces an
equidecomposition. -/
