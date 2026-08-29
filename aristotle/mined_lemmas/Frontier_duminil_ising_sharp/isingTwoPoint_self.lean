/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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
## The finite-volume Ising model

We set up the ferromagnetic Ising model on a finite graph `G` at inverse temperature `β`
with external field `h`: spins `σ : V → Bool` with values `spinVal (σ x) ∈ {-1, +1}`,
Gibbs weights `exp (-β * energy + h * ∑ spins)`, and the associated expectations,
two-point functions and magnetisation.
-/

section IsingFinite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The spin value `±1` attached to a Boolean spin variable. -/

lemma isingTwoPoint_self (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (x : V) :
    isingTwoPoint G β x x = 1 := by
  have hZ : 0 < isingPartition G β 0 := isingPartition_pos G β 0
  simp only [isingTwoPoint, isingExpect, spinVal_mul_self, mul_one]
  rw [← isingPartition, div_self hZ.ne']

end IsingFinite

/-!
## The lattice model

The Ising model on the discrete torus-free box of side `2 * N + 1` in `ℤ ^ d`, and the
infinite-volume two-point function and spontaneous magnetisation obtained as limits.
-/

section Lattice

/-- Sites of the box of side `2 * N + 1` in dimension `d`. -/
abbrev BoxSite (d N : ℕ) : Type := Fin d → Fin (2 * N + 1)

/-- Nearest-neighbour graph on the box: two sites are adjacent when their `ℓ¹`-distance
is `1`. -/
