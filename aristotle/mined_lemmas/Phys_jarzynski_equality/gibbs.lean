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

noncomputable def gibbs (β : ℝ) (H : Ω → ℝ) (x : Ω) : ℝ :=
  Real.exp (-β * H x) / partitionFunction β H

/-- The work performed along the deterministic trajectory started at `x`: the protocol
switches the Hamiltonian from `H₀` to `H₁` while the (Liouville, i.e. phase-space
volume preserving) dynamics carries `x` to `Φ x`. -/
