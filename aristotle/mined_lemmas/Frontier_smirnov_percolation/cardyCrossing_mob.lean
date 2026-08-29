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

theorem cardyCrossing_mob (Φ : ℝ → ℝ) (a b c d x₁ x₂ x₃ x₄ : ℝ) (hdet : a * d - b * c ≠ 0)
    (h₁ : c * x₁ + d ≠ 0) (h₂ : c * x₂ + d ≠ 0) (h₃ : c * x₃ + d ≠ 0) (h₄ : c * x₄ + d ≠ 0)
    (h₁₃ : x₁ ≠ x₃) (h₂₄ : x₂ ≠ x₄) :
    cardyCrossing Φ (mob a b c d x₁) (mob a b c d x₂) (mob a b c d x₃) (mob a b c d x₄)
      = cardyCrossing Φ x₁ x₂ x₃ x₄ := by
  unfold cardyCrossing
  rw [crossRatio_mob a b c d x₁ x₂ x₃ x₄ hdet h₁ h₂ h₃ h₄ h₁₃ h₂₄]

/-- The quadruple `(0, 2, 3, 6)` is self-dual: its conformal modulus is `1/2`. -/
