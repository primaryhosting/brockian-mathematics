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

theorem mobius_lt_mobius {α β γ δ x y : ℝ} (hdet : 0 < α * δ - β * γ)
    (hx : 0 < γ * x + δ) (hy : 0 < γ * y + δ) (hxy : x < y) :
    mobius α β γ δ x < mobius α β γ δ y := by
  have h := mobius_sub (α := α) (β := β) hy.ne' hx.ne'
  have hpos : 0 < (α * δ - β * γ) * (y - x) / ((γ * y + δ) * (γ * x + δ)) :=
    div_pos (by nlinarith) (by positivity)
  linarith [h ▸ hpos]

/-- **Conformal invariance of the modulus.**  The cross-ratio of four boundary points is
invariant under the conformal automorphisms of the upper half plane. -/
