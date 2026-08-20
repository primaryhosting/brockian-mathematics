/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Frontier

/-! ## Conformal rectangles, cross-ratio, and Möbius maps

Smirnov's theorem (Cardy–Smirnov formula) states that for critical site percolation on the
triangular lattice, the probability of a left-right crossing of a conformal rectangle
`(D; z₁, z₂, z₃, z₄)` converges, in the scaling limit, to a quantity that depends only on the
conformal class of the marked domain — equivalently (by the Riemann mapping theorem) only on the
cross-ratio of the four marked boundary points — and is given there by Cardy's hypergeometric
formula.

The analytic content of the scaling limit is beyond what is currently available in Mathlib.
What is formalized and proved here is the *conformal-invariance reduction*: once the limiting
crossing probability is known to be a function of the cross-ratio of the four marked points
(Cardy's formula), conformal invariance of crossing probabilities follows, since the cross-ratio
is invariant under Möbius transformations — the conformal automorphisms of the Riemann sphere. -/

/-- The cross-ratio of four points of `ℂ`, the conformal invariant of a marked domain
`(D; z₁, z₂, z₃, z₄)`. -/

theorem crossRatio_swap (z₁ z₂ z₃ z₄ : ℂ) :
    crossRatio z₂ z₁ z₄ z₃ = crossRatio z₁ z₂ z₃ z₄ := by
  unfold crossRatio
  rw [mul_comm (z₂ - z₄) (z₁ - z₃), mul_comm (z₂ - z₃) (z₁ - z₄)]

/-! ## Conformal invariance of critical crossing probabilities -/

/-- A *crossing-probability model* assigns to a marked domain `(D; z₁, z₂, z₃, z₄)` the
probability of a left-right crossing of `D` between the boundary arcs determined by the four
marked points. -/
abbrev CrossingProbability : Type := Set ℂ → ℂ → ℂ → ℂ → ℂ → ℝ

/-- A crossing-probability model is *conformally invariant* if it is unchanged by applying a
Möbius transformation to the domain and to its marked boundary points. -/
