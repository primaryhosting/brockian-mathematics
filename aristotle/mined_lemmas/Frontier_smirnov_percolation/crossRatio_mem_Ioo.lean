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

theorem crossRatio_mem_Ioo {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    crossRatio a b c d ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold crossRatio
  refine ⟨div_pos (by nlinarith) (by nlinarith), ?_⟩
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-! ## Part 3: the Cardy–Smirnov theorem

`SmirnovConvergence P cardy` is the content of Smirnov's theorem: for critical site
percolation on the triangular lattice of mesh `1/n` inside the upper half plane, the
probability `P n a b c d` of an open crossing between the boundary arcs `[a,b]` and
`[c,d]` converges, as the mesh tends to `0`, to `cardy` evaluated at the conformal modulus
of the marked domain — this is Cardy's formula in Carleson's form. -/

/-- Smirnov's convergence theorem, as a hypothesis on a family `P` of discrete crossing
probabilities and a limit function `cardy` of the conformal modulus. -/
