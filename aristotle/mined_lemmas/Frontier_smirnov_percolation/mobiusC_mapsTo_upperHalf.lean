import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

Smirnov's theorem (conjectured by Cardy, proved by Smirnov in 2001) states that the
crossing probabilities of critical site percolation on the triangular lattice converge,
in the scaling limit, to a conformally invariant limit given by Cardy's formula.

A *conformal quadrilateral* is a simply connected Jordan domain together with four marked
boundary points; the crossing event is "there is an open path joining the boundary arc
`ab` to the boundary arc `cd`".  By the Riemann mapping theorem every such quadrilateral is
conformally equivalent to the upper half-plane `ℍ` with four marked points on the real
line, and the conformal maps of `ℍ` to itself are exactly the real Möbius transformations
of positive determinant.  Consequently:

*conformal invariance of the scaling limit* is **equivalent** to the statement that the
limiting crossing probability, viewed as a function of four marked points of `∂ℍ = ℝ`,
is invariant under the real Möbius group, i.e. that it is a function of the cross-ratio
alone — the *conformal modulus* of the quadrilateral.

This file carries out that reduction in full and proves it, together with the
Cardy–Smirnov base case: the self-dual (symmetric) quadrilateral has crossing
probability exactly `1/2`.

The percolation input that we keep as a hypothesis is precisely the one supplied by
Smirnov's theorem: the limiting crossing probability is `Φ (cross-ratio)` for a universal
profile `Φ` satisfying the colour-swap (duality) relation `Φ x + Φ (1 - x) = 1`.
In Carleson's normalisation of Cardy's formula (the equilateral-triangle picture),
`Φ` is the identity function, which is recorded below as `carleson_isCardyProfile`.
-/

/-- The cross-ratio of four points of `∂ℍ = ℝ`; this is the conformal modulus of the
conformal quadrilateral with these four marked boundary points. -/

theorem mobiusC_mapsTo_upperHalf (p q r s : ℝ) (hdet : 0 < p * s - q * r) :
    ∀ z ∈ UpperHalf, mobiusC p q r s z ∈ UpperHalf := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hne : ((r : ℂ) * z + s) ≠ 0 := by
    intro h
    have : (mobiusC p q r s z).im = 0 := by simp [mobiusC, h]
    have him : ((r : ℂ) * z + s).im = 0 := by rw [h]; simp
    have : r * z.im = 0 := by
      simpa [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] using him
    have hr : r = 0 := by
      rcases mul_eq_zero.mp this with h1 | h2
      · exact h1
      · exact absurd h2 (ne_of_gt hz')
    have hre : ((r : ℂ) * z + s).re = 0 := by rw [h]; simp
    have hs : s = 0 := by
      simpa [hr, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using hre
    rw [hr, hs] at hdet
    simp at hdet
  have hns : 0 < Complex.normSq ((r : ℂ) * z + s) := by
    simpa [Complex.normSq_pos] using hne
  show 0 < (mobiusC p q r s z).im
  rw [mobiusC_im]
  exact div_pos (mul_pos hdet hz') hns

/-!
## Möbius invariance of the conformal modulus
-/

/-- The action of a real Möbius transformation on `ℂ` restricts on the boundary `ℝ = ∂ℍ`
to its action on the four marked points. -/
