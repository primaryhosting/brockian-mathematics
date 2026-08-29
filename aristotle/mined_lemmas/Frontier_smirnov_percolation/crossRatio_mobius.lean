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

theorem crossRatio_mobius {α β γ δ a b c d : ℝ} (hdet : α * δ - β * γ ≠ 0)
    (ha : γ * a + δ ≠ 0) (hb : γ * b + δ ≠ 0) (hc : γ * c + δ ≠ 0) (hd : γ * d + δ ≠ 0)
    (hca : c ≠ a) (hdb : d ≠ b) :
    crossRatio (mobius α β γ δ a) (mobius α β γ δ b) (mobius α β γ δ c) (mobius α β γ δ d)
      = crossRatio a b c d := by
  have hca' : c - a ≠ 0 := sub_ne_zero.mpr hca
  have hdb' : d - b ≠ 0 := sub_ne_zero.mpr hdb
  unfold crossRatio
  rw [mobius_sub hb ha, mobius_sub hd hc, mobius_sub hc ha, mobius_sub hd hb]
  field_simp

/-- The modulus of a genuine conformal rectangle lies in `(0,1)`, the domain on which
Cardy's function is defined. -/
