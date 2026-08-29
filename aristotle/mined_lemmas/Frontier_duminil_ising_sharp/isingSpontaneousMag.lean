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

noncomputable def isingSpontaneousMag (d : ℕ) (β : ℝ) : ℝ :=
  Filter.limsup
    (fun h : ℝ => Filter.limsup
      (fun N : ℕ => isingMagAt (boxGraph d N) β h (boxCentre d N)) Filter.atTop)
    (nhdsWithin 0 (Set.Ioi 0))

end Lattice

/-!
## The two analytic cores of the Duminil-Copin–Tassion argument

Below `corr β n` stands for the infinite-volume two-point function at distance `n`
and `mag β` for the spontaneous magnetisation.
-/

/-- **Geometric bound from the subcritical recursion.** If a nonnegative sequence bounded
by `1` satisfies the `L`-step contraction `a (n + L) ≤ c * a n`, then `a n ≤ c ^ ⌊n / L⌋`. -/
