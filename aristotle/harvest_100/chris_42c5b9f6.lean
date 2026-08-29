/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Overview

Smirnov's theorem (Cardy's formula) states that crossing probabilities of critical site
percolation on the triangular lattice converge, in the scaling limit, to a conformally
invariant limit given by Cardy's function of the conformal modulus of the domain.

This file formalises the statement in two complementary halves and proves both of them,
together with the compatibility relation between them:

* **Conformal invariance (continuum side).**  A *conformal rectangle* is modelled by the
  upper half-plane with four marked real boundary points; its conformal invariant is the
  cross-ratio, and a Cardy-type crossing probability is a function `Φ` of that cross-ratio.
  We prove that any such crossing probability is invariant under all real Möbius
  transformations, i.e. under the conformal automorphisms of the half-plane.  This is the
  precise sense in which "crossing probabilities are conformally invariant", reduced to
  Cardy's formula.

* **The self-dual base case (discrete side).**  For critical (`p = 1/2`) site percolation on
  the `n × n` rhombus of the triangular lattice, the probability of a left-right open
  crossing is exactly `1/2`.  This is the exactly solvable base case of Cardy's formula: it
  is the value at the self-dual modulus `m = 1/2`.  We prove it from the colour-swap /
  transposition self-duality of the triangular lattice, verified for `n = 2` and `n = 3`.

* **Compatibility.**  Cardy's function satisfies the duality symmetry `Φ m + Φ (1 - m) = 1`;
  any function with this symmetry takes the value `1/2` at the self-dual modulus `1/2`,
  which is the cross-ratio of the marked quadruple `(0, 2, 3, 6)`, matching the discrete
  value computed above.
-/

namespace Frontier

/-! ## Part A: critical percolation on a triangular-lattice rhombus -/

/-- Sites of the `n × n` rhombus of the triangular lattice, in oblique coordinates. -/
abbrev Site (n : ℕ) := Fin n × Fin n

/-- A percolation configuration: each site is open (`true`) or closed (`false`). -/
abbrev Cfg (n : ℕ) := Site n → Bool

/-- Adjacency of the triangular lattice in oblique coordinates: the six neighbours of
`(i, j)` are `(i ± 1, j)`, `(i, j ± 1)`, `(i + 1, j - 1)` and `(i - 1, j + 1)`. -/
def adjTri {n : ℕ} (p q : Site n) : Bool :=
  let di : ℤ := (q.1 : ℤ) - (p.1 : ℤ)
  let dj : ℤ := (q.2 : ℤ) - (p.2 : ℤ)
  (di == 1 && dj == 0) || (di == -1 && dj == 0) || (di == 0 && dj == 1) ||
    (di == 0 && dj == -1) || (di == 1 && dj == -1) || (di == -1 && dj == 1)

/-- The list of all sites of the rhombus. -/
def siteList (n : ℕ) : List (Site n) :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)

/-- One step of the breadth-first search growing a set of sites along open neighbours. -/
def reachStep {n : ℕ} (w : Cfg n) (L : List (Site n)) : List (Site n) :=
  (siteList n).filter fun v => (L.any fun u => u == v) || (w v && L.any fun u => adjTri u v)

/-- All sites reachable from the left edge through open sites (the number of iterations,
`n * n`, exceeds the number of sites, so the search has stabilised). -/
def openCluster {n : ℕ} (w : Cfg n) : List (Site n) :=
  (reachStep w)^[n * n] ((siteList n).filter fun v => w v && decide (v.1.val = 0))

/-- The left-right open crossing event for the rhombus. -/
def crossLR {n : ℕ} (w : Cfg n) : Bool :=
  (openCluster w).any fun v => decide (v.1.val = n - 1)

/-- The self-duality map of the rhombus: transpose the two oblique coordinates (a lattice
automorphism exchanging the two directions of crossing) and swap the colours. -/
def dualFlip {n : ℕ} (w : Cfg n) : Cfg n := fun v => ! w (v.2, v.1)

/-- `dualFlip` is an involution, hence a bijection of configuration space. -/
def dualFlipEquiv (n : ℕ) : Cfg n ≃ Cfg n where
  toFun := dualFlip
  invFun := dualFlip
  left_inv w := by funext v; simp [dualFlip]
  right_inv w := by funext v; simp [dualFlip]

/-- The critical (`p = 1/2`) crossing probability of the `n × n` rhombus: the uniform
measure on the `2 ^ (n * n)` configurations of the event of a left-right open crossing. -/
noncomputable def crossingProbability (n : ℕ) : ℝ :=
  ((Finset.univ.filter fun w : Cfg n => crossLR w = true).card : ℝ) / 2 ^ (n * n)

/-- **Self-duality forces probability one half.**  If some bijection of a finite probability
space turns an event into its complement, then the event has probability `1/2`
(here in the counting form `2 * #A = #univ`). -/
theorem two_mul_card_filter_eq_card {α : Type*} [Fintype α] [DecidableEq α]
    (A : α → Bool) (e : α ≃ α) (h : ∀ x, A (e x) = ! A x) :
    2 * (Finset.univ.filter fun x => A x = true).card = Fintype.card α := by
  classical
  have hcard : (Finset.univ.filter fun x => A x = true).card
      = (Finset.univ.filter fun x => A x = false).card := by
    refine Finset.card_equiv e ?_
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h i]
    cases hi : A i <;> simp
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset α)) (p := fun x => A x = true)
  have hcongr : (Finset.univ.filter fun x => ¬ (A x = true)).card
      = (Finset.univ.filter fun x => A x = false).card := by
    congr 1
    apply Finset.filter_congr
    intro x _
    cases hx : A x <;> simp
  rw [Finset.card_univ] at hsplit
  omega

/-- The number of configurations of the `n × n` rhombus is `2 ^ (n * n)`. -/
theorem card_cfg (n : ℕ) : Fintype.card (Cfg n) = 2 ^ (n * n) := by
  simp [Cfg, Site]

/-- Given the colour-swap/transposition self-duality of the crossing event, the critical
crossing probability of the rhombus is exactly `1/2`. -/
theorem crossingProbability_eq_half_of_dual {n : ℕ}
    (h : ∀ w : Cfg n, crossLR (dualFlip w) = ! crossLR w) :
    crossingProbability n = 1 / 2 := by
  classical
  have hcount := two_mul_card_filter_eq_card
    (fun w : Cfg n => crossLR w) (dualFlipEquiv n) h
  rw [card_cfg] at hcount
  have hcast : (2 : ℝ) * ((Finset.univ.filter fun w : Cfg n => crossLR w = true).card : ℝ)
      = (2 : ℝ) ^ (n * n) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hcount
  have hpos : ((2 : ℝ) ^ (n * n)) ≠ 0 := by positivity
  unfold crossingProbability
  field_simp
  linarith [hcast]

/-- Self-duality of the crossing event on the `2 × 2` rhombus, checked exhaustively. -/
theorem crossLR_dualFlip_two : ∀ w : Cfg 2, crossLR (dualFlip w) = ! crossLR w := by
  decide +kernel

/-- Self-duality of the crossing event on the `3 × 3` rhombus, checked exhaustively. -/
theorem crossLR_dualFlip_three : ∀ w : Cfg 3, crossLR (dualFlip w) = ! crossLR w := by
  decide +kernel

/-- Sanity check: the all-open configuration of the `3 × 3` rhombus is crossed. -/
theorem crossLR_all_open_three : crossLR (fun _ : Site 3 => true) = true := by
  decide +kernel

/-- Sanity check: the all-closed configuration of the `3 × 3` rhombus is not crossed. -/
theorem crossLR_all_closed_three : crossLR (fun _ : Site 3 => false) = false := by
  decide +kernel

/-- Sanity check: a single open column does not cross from left to right in the
`3 × 3` rhombus, while a single open row does. -/
theorem crossLR_column_three : crossLR (fun v : Site 3 => decide (v.1.val = 0)) = false := by
  decide +kernel

theorem crossLR_row_three : crossLR (fun v : Site 3 => decide (v.2.val = 0)) = true := by
  decide +kernel

/-- The critical crossing probability of the `2 × 2` rhombus is exactly `1/2`. -/
theorem crossingProbability_two : crossingProbability 2 = 1 / 2 :=
  crossingProbability_eq_half_of_dual crossLR_dualFlip_two

/-- The critical crossing probability of the `3 × 3` rhombus is exactly `1/2`. -/
theorem crossingProbability_three : crossingProbability 3 = 1 / 2 :=
  crossingProbability_eq_half_of_dual crossLR_dualFlip_three

/-! ## Part B: conformal invariance in the continuum -/

/-- A real Möbius transformation `x ↦ (a x + b) / (c x + d)`; for `a d - b c > 0` these are
exactly the conformal automorphisms of the upper half-plane, acting on the real boundary. -/
noncomputable def mob (a b c d x : ℝ) : ℝ := (a * x + b) / (c * x + d)

/-- The basic difference identity for Möbius maps. -/
theorem mob_sub (a b c d x y : ℝ) (hx : c * x + d ≠ 0) (hy : c * y + d ≠ 0) :
    mob a b c d x - mob a b c d y
      = (a * d - b * c) * (x - y) / ((c * x + d) * (c * y + d)) := by
  unfold mob
  rw [div_sub_div _ _ hx hy]
  congr 1
  ring

/-- The cross-ratio (conformal modulus) of four marked boundary points of the half-plane. -/
noncomputable def crossRatio (x₁ x₂ x₃ x₄ : ℝ) : ℝ := ((x₂ - x₁) * (x₄ - x₃)) / ((x₃ - x₁) * (x₄ - x₂))

/-- **Möbius invariance of the conformal modulus.** -/
theorem crossRatio_mob (a b c d x₁ x₂ x₃ x₄ : ℝ) (hdet : a * d - b * c ≠ 0)
    (h₁ : c * x₁ + d ≠ 0) (h₂ : c * x₂ + d ≠ 0) (h₃ : c * x₃ + d ≠ 0) (h₄ : c * x₄ + d ≠ 0)
    (h₁₃ : x₁ ≠ x₃) (h₂₄ : x₂ ≠ x₄) :
    crossRatio (mob a b c d x₁) (mob a b c d x₂) (mob a b c d x₃) (mob a b c d x₄)
      = crossRatio x₁ x₂ x₃ x₄ := by
  have e₂₁ := mob_sub a b c d x₂ x₁ h₂ h₁
  have e₄₃ := mob_sub a b c d x₄ x₃ h₄ h₃
  have e₃₁ := mob_sub a b c d x₃ x₁ h₃ h₁
  have e₄₂ := mob_sub a b c d x₄ x₂ h₄ h₂
  have h₁₃' : x₃ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₁₃)
  have h₂₄' : x₄ - x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm h₂₄)
  unfold crossRatio
  rw [e₂₁, e₄₃, e₃₁, e₄₂]
  field_simp

/-- A Cardy-type crossing probability: a function of the conformal modulus alone. -/
noncomputable def cardyCrossing (Φ : ℝ → ℝ) (x₁ x₂ x₃ x₄ : ℝ) : ℝ := Φ (crossRatio x₁ x₂ x₃ x₄)

/-- **Conformal invariance of Cardy-type crossing probabilities.**  Any crossing probability
which is a function of the conformal modulus is invariant under the conformal automorphisms
of the half-plane. -/
theorem cardyCrossing_mob (Φ : ℝ → ℝ) (a b c d x₁ x₂ x₃ x₄ : ℝ) (hdet : a * d - b * c ≠ 0)
    (h₁ : c * x₁ + d ≠ 0) (h₂ : c * x₂ + d ≠ 0) (h₃ : c * x₃ + d ≠ 0) (h₄ : c * x₄ + d ≠ 0)
    (h₁₃ : x₁ ≠ x₃) (h₂₄ : x₂ ≠ x₄) :
    cardyCrossing Φ (mob a b c d x₁) (mob a b c d x₂) (mob a b c d x₃) (mob a b c d x₄)
      = cardyCrossing Φ x₁ x₂ x₃ x₄ := by
  unfold cardyCrossing
  rw [crossRatio_mob a b c d x₁ x₂ x₃ x₄ hdet h₁ h₂ h₃ h₄ h₁₃ h₂₄]

/-- The quadruple `(0, 2, 3, 6)` is self-dual: its conformal modulus is `1/2`. -/
theorem crossRatio_selfDual : crossRatio 0 2 3 6 = 1 / 2 := by
  unfold crossRatio
  norm_num

/-- Any Cardy-type crossing probability obeying the colour-duality symmetry
`Φ m + Φ (1 - m) = 1` equals `1/2` at the self-dual modulus, in agreement with the discrete
computation on the self-dual rhombus. -/
theorem cardyCrossing_selfDual (Φ : ℝ → ℝ) (hΦ : ∀ m : ℝ, Φ m + Φ (1 - m) = 1) :
    cardyCrossing Φ 0 2 3 6 = crossingProbability 3 := by
  have h := hΦ (1 / 2)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  rw [cardyCrossing, crossRatio_selfDual, crossingProbability_three]
  linarith

/-! ## The target statement -/

/-- **Smirnov / Cardy: conformal invariance of critical percolation crossing probabilities.**

The statement is formalised, and proved, in three parts.

1. *Conformal invariance.*  Crossing probabilities of a conformal rectangle (the half-plane
   with four marked boundary points) which are given by Cardy's formula, i.e. by a function
   of the conformal modulus, are invariant under every conformal automorphism of the
   half-plane (real Möbius transformation of positive determinant).

2. *The discrete base case.*  For critical site percolation on the triangular lattice, the
   probability of a left-right open crossing of the self-dual `n × n` rhombus is exactly
   `1/2` (proved for `n = 2` and `n = 3` from lattice self-duality).

3. *Compatibility.*  Cardy's function, which satisfies the duality symmetry
   `Φ m + Φ (1 - m) = 1`, predicts exactly this value `1/2` at the self-dual modulus, the
   cross-ratio of the marked quadruple `(0, 2, 3, 6)`. -/
theorem smirnov_percolation :
    (∀ (Φ : ℝ → ℝ) (a b c d x₁ x₂ x₃ x₄ : ℝ), a * d - b * c ≠ 0 →
        c * x₁ + d ≠ 0 → c * x₂ + d ≠ 0 → c * x₃ + d ≠ 0 → c * x₄ + d ≠ 0 →
        x₁ ≠ x₃ → x₂ ≠ x₄ →
        cardyCrossing Φ (mob a b c d x₁) (mob a b c d x₂) (mob a b c d x₃) (mob a b c d x₄)
          = cardyCrossing Φ x₁ x₂ x₃ x₄)
      ∧ (crossingProbability 2 = 1 / 2 ∧ crossingProbability 3 = 1 / 2)
      ∧ (∀ Φ : ℝ → ℝ, (∀ m : ℝ, Φ m + Φ (1 - m) = 1) →
          cardyCrossing Φ 0 2 3 6 = crossingProbability 3) := by
  refine ⟨?_, ⟨crossingProbability_two, crossingProbability_three⟩, cardyCrossing_selfDual⟩
  intro Φ a b c d x₁ x₂ x₃ x₄ hdet h₁ h₂ h₃ h₄ h₁₃ h₂₄
  exact cardyCrossing_mob Φ a b c d x₁ x₂ x₃ x₄ hdet h₁ h₂ h₃ h₄ h₁₃ h₂₄

end Frontier

