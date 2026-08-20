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

def work (H₀ H₁ : S → ℝ) (T : S ≃ S) (x : S) : ℝ := H₁ (T x) - H₀ x

