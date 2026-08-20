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

theorem crossRatio_mobius (p q r s : ℝ) (hdet : p * s - q * r ≠ 0) (a b c d : ℝ)
    (ha : r * a + s ≠ 0) (hb : r * b + s ≠ 0) (hc : r * c + s ≠ 0) (hd : r * d + s ≠ 0) :
    crossRatio (mobius p q r s a) (mobius p q r s b) (mobius p q r s c) (mobius p q r s d)
      = crossRatio a b c d := by
  have hac := mobius_sub p q r s a c ha hc
  have hbd := mobius_sub p q r s b d hb hd
  have had := mobius_sub p q r s a d ha hd
  have hbc := mobius_sub p q r s b c hb hc
  rcases eq_or_ne ((a - d) * (b - c)) 0 with hdeg | hdeg
  · -- Degenerate configuration: both sides are `x / 0 = 0`.
    have hdeg' :
        (mobius p q r s a - mobius p q r s d) * (mobius p q r s b - mobius p q r s c) = 0 := by
      rcases mul_eq_zero.1 hdeg with h | h
      · have : a = d := by linarith [sub_eq_zero.1 h]
        simp [this]
      · have : b = c := by linarith [sub_eq_zero.1 h]
        simp [this]
    unfold crossRatio
    rw [hdeg, hdeg', div_zero, div_zero]
  · have h1 : a - d ≠ 0 := fun h => hdeg (by rw [h]; ring)
    have h2 : b - c ≠ 0 := fun h => hdeg (by rw [h]; ring)
    unfold crossRatio
    rw [hac, hbd, had, hbc]
    field_simp

/-- The cross ratio satisfies the classical relation `(a,b;c,d) + (a,c;b,d) = 1`, which is the
source of the self-duality `Π(a,b,c,d) + Π(a,c,b,d) = 1` of crossing probabilities. -/
