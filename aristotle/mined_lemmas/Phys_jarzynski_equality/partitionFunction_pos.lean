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

lemma partitionFunction_pos (beta : ℝ) (H : X → ℝ) : 0 < partitionFunction beta H := by
  refine Finset.sum_pos (fun x _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- **Jarzynski equality.**  For a finite phase space, a system started in the Boltzmann
distribution of `H₀` and driven by an arbitrary phase-space bijection `T` (Liouville's
theorem) while the Hamiltonian is switched from `H₀` to `H₁`, the exponential average of
the work equals `e^{−β ΔF}`, where `ΔF = F(H₁) − F(H₀)` is the equilibrium free energy
difference. -/
