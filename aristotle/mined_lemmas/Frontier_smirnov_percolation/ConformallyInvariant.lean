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

def ConformallyInvariant (P : CrossingProbability) : Prop :=
  ∀ (a b c d : ℂ), a * d - b * c ≠ 0 → ∀ (D : Set ℂ) (z₁ z₂ z₃ z₄ : ℂ),
    c * z₁ + d ≠ 0 → c * z₂ + d ≠ 0 → c * z₃ + d ≠ 0 → c * z₄ + d ≠ 0 →
    P (mobius a b c d '' D) (mobius a b c d z₁) (mobius a b c d z₂) (mobius a b c d z₃)
        (mobius a b c d z₄) = P D z₁ z₂ z₃ z₄

/-- **Cardy–Smirnov, conformal-invariance reduction.**

If the scaling limit `P` of the crossing probabilities of critical triangular-lattice percolation
is given by Cardy's formula — i.e. `P D z₁ z₂ z₃ z₄ = Cardy (crossRatio z₁ z₂ z₃ z₄)` for some
function `Cardy` of the cross-ratio alone — then `P` is conformally invariant: it is unchanged
under every Möbius transformation of the marked domain.

This is the Lean-checked reduction of Smirnov's conformal-invariance theorem to Cardy's formula;
its proof is the Möbius invariance of the cross-ratio (`Frontier.crossRatio_mobius`). -/
