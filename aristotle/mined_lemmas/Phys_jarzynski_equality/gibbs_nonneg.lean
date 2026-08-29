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

theorem gibbs_nonneg (β : ℝ) (H : Ω → ℝ) (x : Ω) : 0 ≤ gibbs β H x :=
  div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

/-- **Second law of thermodynamics** as a corollary of the Jarzynski equality:
the average work done on the system is at least the free-energy difference,
`⟨W⟩ ≥ ΔF`.  (Obtained from `⟨e^{-βW}⟩ = e^{-βΔF}` by Jensen's inequality.) -/
