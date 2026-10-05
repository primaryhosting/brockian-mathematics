import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

section Setup

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Partition function of the energy landscape `E k` at inverse temperature `beta`. -/

def reversePath (N : ℕ) (x : ℕ → X) : ℕ → X := fun j => x (N - j)

/-- Free-energy difference between the final and the initial equilibrium ensembles. -/
