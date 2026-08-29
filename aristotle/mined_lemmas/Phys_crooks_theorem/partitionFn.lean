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

noncomputable def partitionFn (E : ℕ → X → ℝ) (beta : ℝ) (k : ℕ) : ℝ :=
  ∑ x : X, Real.exp (-beta * E k x)

