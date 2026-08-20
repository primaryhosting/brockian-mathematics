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

noncomputable def gibbs (beta : ℝ) (H : X → ℝ) (x : X) : ℝ :=
  Real.exp (-beta * H x) / partitionFunction beta H

/-- The work performed along the trajectory starting at `x`, where the (Liouville,
i.e. measure preserving) protocol carries `x` to `T x` while the Hamiltonian is
switched from `H₀` to `H₁`. -/
