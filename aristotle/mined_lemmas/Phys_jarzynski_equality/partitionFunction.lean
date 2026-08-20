import Mathlib

/-!
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Statement: ⟨e^{−βW}⟩ = e^{−βΔF} for nonequilibrium work (Jarzynski).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {X : Type*} [Fintype X] [Nonempty X]

/-- The canonical partition function `Z(β, H) = ∑ₓ e^{−β H(x)}` of a Hamiltonian `H`
on a finite phase space `X` at inverse temperature `β`. -/

noncomputable def partitionFunction (beta : ℝ) (H : X → ℝ) : ℝ :=
  ∑ x : X, Real.exp (-beta * H x)

/-- The Helmholtz free energy `F = −(1/β) log Z`. -/
