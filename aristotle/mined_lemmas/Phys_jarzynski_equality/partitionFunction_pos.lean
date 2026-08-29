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

lemma partitionFunction_pos [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) :
    0 < partitionFunction β H := by
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

/-- **Jarzynski equality.** For a system prepared in the Gibbs state of `H₀` and driven by an
arbitrary volume-preserving (Liouville) evolution `Φ` while the Hamiltonian is switched to `H₁`,
the exponential average of the work equals `e^{-βΔF}`, where `ΔF = F₁ - F₀` is the free-energy
difference between the equilibrium states of the two Hamiltonians. -/
