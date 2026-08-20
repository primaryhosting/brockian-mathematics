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

noncomputable def partition (beta : ℝ) (H : S → ℝ) : ℝ := ∑ x, Real.exp (-beta * H x)

/-- Boltzmann (equilibrium) probability of the state `x`. -/
