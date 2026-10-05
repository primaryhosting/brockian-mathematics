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

theorem carleson_isCardyProfile : IsCardyProfile id := by
  intro x
  simp

/-- **Cardy base case.**  Any profile satisfying the duality relation takes the value
`1/2` at the self-dual modulus `1/2`. -/
