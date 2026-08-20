/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-!
## Setting

Cardy's formula, as proved by Smirnov for critical site percolation on the triangular
lattice, says the following.  Take a Jordan domain `Ω` with four marked boundary points
`a, b, c, d` in cyclic order, and let `Π(Ω; a, b, c, d)` be the scaling limit of the
probability that the arc `ab` is joined to the arc `cd` by an open cluster.  Then `Π`
depends only on the conformal class of the configuration `(Ω; a, b, c, d)`; concretely,
after uniformizing `Ω` onto the upper half plane `ℍ` (so that the marked points sit on
the real line), `Π` is a fixed function `F` of the *cross-ratio* of the four marked
points.

The two ingredients are therefore:

* **Cardy's formula** (`cardy` below): in the half-plane normalization the crossing
  probability is a function of the cross ratio alone;
* **conformal invariance**: the conformal automorphisms of `ℍ` are the real Möbius maps
  with positive determinant, and the crossing probability is unchanged by them.

What is formalized here is the *reduction* of conformal invariance to Cardy's formula:
granted that the limiting crossing probability has the Cardy form, it is invariant under
every Möbius change of coordinates of the half-plane (`Frontier.smirnov_percolation`), and
it automatically satisfies the self-duality relation
`Π(a,b,c,d) + Π(a,c,b,d) = 1` (`Frontier.crossing_duality`).  The analytic heart of the
reduction is the Möbius invariance of the cross ratio, proved below from scratch.
-/

/-- The cross ratio `(a, b ; c, d) = ((a - c)(b - d)) / ((a - d)(b - c))` of four points of
the real line, thought of as marked boundary points of the upper half plane. -/

theorem smirnov_percolation_translation
    (crossingProb : ℝ → ℝ → ℝ → ℝ → ℝ) (hCardy : IsCardy crossingProb) (t a b c d : ℝ) :
    crossingProb (a + t) (b + t) (c + t) (d + t) = crossingProb a b c d := by
  have h := smirnov_percolation crossingProb hCardy 1 t 0 1 (by norm_num) a b c d
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa [mobius, add_comm] using h

/-- Base case: dilations `z ↦ k z` with `k ≠ 0` leave the crossing probability unchanged. -/
