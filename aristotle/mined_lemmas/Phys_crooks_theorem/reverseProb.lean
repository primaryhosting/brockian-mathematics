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

noncomputable def reverseProb (E : ℕ → X → ℝ) (T : ℕ → X → X → ℝ) (beta : ℝ) (N : ℕ)
    (y : ℕ → X) : ℝ :=
  Real.exp (-beta * E N (y 0)) / partitionFn E beta N *
    ∏ j ∈ Finset.range N, T (N - 1 - j) (y j) (y (j + 1))

/-- Time reversal of a trajectory of length `N`. -/
