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

theorem cardy_mem_Icc (P : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ) (cardy : ℝ → ℝ)
    (hSmirnov : SmirnovConvergence P cardy)
    (hP : ∀ n a b c d, P n a b c d ∈ Set.Icc (0 : ℝ) 1)
    {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    cardy (crossRatio a b c d) ∈ Set.Icc (0 : ℝ) 1 := by
  have hlim := hSmirnov a b c d hab hbc hcd
  exact ⟨ge_of_tendsto' hlim (fun n => (hP n a b c d).1),
    le_of_tendsto' hlim (fun n => (hP n a b c d).2)⟩

end Frontier

