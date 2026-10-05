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

set_option grind.warning false

namespace Frontier

open Filter Topology

/-! ## Part 1: the discrete model (critical site percolation, `p = 1/2`)

Site percolation on a finite site set `V` (a finite piece of the triangular lattice) is
modelled as a uniformly random colouring `ω : V → Bool`, with `true` meaning *open*.  On
the triangular lattice the critical parameter is `p_c = 1/2`, so the uniform measure on
colourings is exactly the critical percolation measure. -/

section Discrete

variable {V : Type*} [Fintype V]

/-- The probability of an event `E` of percolation configurations under critical
(`p = 1/2`) site percolation on the finite site set `V`. -/

theorem probHalf_openCrossing_eq_closedCrossing
    (adj : V → V → Prop) (A B : Finset V) :
    probHalf (OpenCrossing adj A B) = probHalf (ClosedCrossing adj A B) := by
  rw [probHalf_flip (OpenCrossing adj A B)]
  congr 1
  funext ω
  exact propext (closedCrossing_iff_openCrossing_flip adj A B ω).symm

end Discrete

/-! ## Part 2: the conformal modulus of a marked domain

A conformal rectangle is encoded as the upper half plane with four marked boundary points
`a < b < c < d` on the real line, the two boundary arcs to be crossed being `[a,b]` and
`[c,d]`.  Its conformal modulus is the cross-ratio of the four marked points; the
conformal automorphisms of the upper half plane act on the boundary by real Möbius maps
of positive determinant. -/

/-- The cross-ratio (conformal modulus) of four boundary points of the upper half plane. -/
