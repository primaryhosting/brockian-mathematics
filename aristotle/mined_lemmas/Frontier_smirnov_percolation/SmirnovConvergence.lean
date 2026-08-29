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

def SmirnovConvergence (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ) (cardy : ℝ → ℝ) : Prop :=
  ∀ a b c d : ℝ, a < b → b < c → c < d →
    Tendsto (fun n => P n a b c d) atTop (𝓝 (cardy (crossRatio a b c d)))

/-- **Cardy–Smirnov conformal invariance of crossing probabilities.**

Assume Smirnov's theorem `SmirnovConvergence P cardy`, i.e. that the discrete crossing
probabilities of critical triangular-lattice percolation between the boundary arcs `[a,b]`
and `[c,d]` of the upper half plane converge, as the mesh tends to `0`, to a function of
the conformal modulus of the marked domain.

Then the limiting crossing probability is conformally invariant: for every conformal
automorphism `g` of the upper half plane (a real Möbius map of positive determinant, here
assumed pole-free on the interval carrying the marked points), the crossing probabilities
of the image configuration `(g a, g b, g c, g d)` converge to the *same* limit as those of
`(a, b, c, d)`. -/
