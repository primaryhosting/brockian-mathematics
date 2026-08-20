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

noncomputable def boltzmann (beta : ℝ) (H : S → ℝ) (x : S) : ℝ :=
  Real.exp (-beta * H x) / partition beta H

/-- Helmholtz free energy `F = -(1/β) log Z`. -/
