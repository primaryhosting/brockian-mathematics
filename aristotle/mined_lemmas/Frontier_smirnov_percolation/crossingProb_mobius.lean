import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Cardy–Smirnov theory says that the scaling limit of crossing probabilities for critical
site percolation on the triangular lattice is *conformally invariant*, and that in the
reference domain — Carleson's equilateral triangle — the limiting crossing probability is
the linear (barycentric) function, so that the crossing probability between the side `AB`
and the sub-segment `CX` of the side `CA` equals `|CX| / |CA|`.

This file formalizes the two structural halves of that statement and proves them:

* **Conformal invariance / reduction.** The conformal modulus of a configuration of four
  marked boundary points is the cross-ratio; it is invariant under Möbius transformations,
  hence any crossing functional that is a function of the modulus is conformally invariant.
  This is the reduction step: the whole Cardy–Smirnov formula is determined by its value on
  one reference configuration.

* **Base case (Carleson's equilateral triangle).** The three Cardy–Smirnov functions
  `smirnovA, smirnovB, smirnovC` attached to the equilateral triangle with vertices
  `A = 0`, `B = 1`, `C = 1/2 + i √3 / 2` are harmonic on the whole plane, sum to `1`,
  take the value `1` at their own vertex and vanish on the opposite side, and satisfy
  Cardy's formula `smirnovA X = |CX| / |CA|` for `X` on the side `CA`.

The probabilistic input of Smirnov's theorem (existence of the scaling limit for critical
site percolation on the triangular lattice) is *not* formalized here; what is formalized
and proved is the conformal-invariance reduction together with the closed form of the
limit in the reference triangle.
-/

namespace Frontier

open Complex

/-! ### The conformal modulus of four marked boundary points -/

/-- The cross-ratio of four points of the plane.  For a Jordan domain with four marked
boundary points this is the conformal modulus of the configuration. -/

theorem crossingProb_mobius (F : ℂ → ℝ) (m : Mobius) {z₁ z₂ z₃ z₄ : ℂ}
    (h₁ : m.c * z₁ + m.d ≠ 0) (h₂ : m.c * z₂ + m.d ≠ 0)
    (h₃ : m.c * z₃ + m.d ≠ 0) (h₄ : m.c * z₄ + m.d ≠ 0)
    (h₁₄ : z₁ ≠ z₄) (h₂₃ : z₂ ≠ z₃) :
    crossingProb F (m z₁) (m z₂) (m z₃) (m z₄) = crossingProb F z₁ z₂ z₃ z₄ := by
  unfold crossingProb
  rw [crossRatio_mobius m h₁ h₂ h₃ h₄ h₁₄ h₂₃]

/-! ### Carleson's equilateral triangle and the Cardy–Smirnov functions -/

/-- Vertex `A` of the reference equilateral triangle. -/
