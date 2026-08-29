/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- The canonical partition function `Z = ∑ₓ e^{-βH(x)}` of a Hamiltonian `H`
on a finite phase space at inverse temperature `β`. -/

noncomputable def freeEnergyOn (μ : Measure Ω) (β : ℝ) (H : Ω → ℝ) : ℝ :=
  -(Real.log (partitionFunctionOn μ β H)) / β

/-- Equilibrium (Boltzmann–Gibbs) density with respect to `μ`. -/
