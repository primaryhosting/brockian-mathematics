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

/-- Canonical partition function `Z = ∑ₓ e^{-βH(x)}` of a Hamiltonian `H` on a finite
state space at inverse temperature `β`. -/

noncomputable def freeEnergy (β : ℝ) (H : Ω → ℝ) : ℝ :=
  -(1 / β) * Real.log (partitionFunction β H)

/-- The Gibbs (canonical equilibrium) distribution `p(x) = e^{-βH(x)}/Z`. -/
