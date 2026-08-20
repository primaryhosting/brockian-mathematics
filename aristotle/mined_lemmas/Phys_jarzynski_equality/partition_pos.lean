/-
# Jarzynski Equality
Category: Frontier Phys
Target: Phys.jarzynski_equality
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Canonical partition function at inverse temperature `β` for energy function `H`. -/

lemma partition_pos (beta : ℝ) (H : S → ℝ) : 0 < partition beta H :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

/-- **Jarzynski equality.**  For a system initially in thermal equilibrium with respect to
`H₀` at inverse temperature `β ≠ 0`, evolving under a deterministic, phase-space-volume
preserving (i.e. bijective) protocol `T` while the Hamiltonian is switched from `H₀` to `H₁`,
the average of `exp (-β W)` over the initial equilibrium ensemble equals `exp (-β ΔF)`,
where `ΔF = F₁ - F₀` is the equilibrium free-energy difference. -/
