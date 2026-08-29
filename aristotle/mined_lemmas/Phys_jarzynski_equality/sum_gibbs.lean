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

theorem sum_gibbs [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) : ∑ x, gibbs β H x = 1 := by
  simp only [gibbs]
  rw [← Finset.sum_div, ← partitionFunction]
  exact div_self (partitionFunction_pos β H).ne'

