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

noncomputable def freeEnergy (beta : ℝ) (H : S → ℝ) : ℝ :=
  -(1 / beta) * Real.log (partition beta H)

/-- The work done along the deterministic protocol taking `x` to `T x`,
while the Hamiltonian is switched from `H₀` to `H₁`. -/
