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

noncomputable def partitionFunction (β : ℝ) (H : Ω → ℝ) : ℝ :=
  ∑ x : Ω, Real.exp (-β * H x)

/-- Helmholtz free energy `F = -(1/β) log Z`. -/
