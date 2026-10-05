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

noncomputable def gibbsKernel (E : ℕ → X → ℝ) (beta : ℝ) (k : ℕ) (_a b : X) : ℝ :=
  Real.exp (-beta * E (k + 1) b) / partitionFn E beta (k + 1)

omit [Nonempty X] in
/-- The Gibbs kernels satisfy detailed balance, so the hypotheses of Crooks' theorem are
non-vacuous. -/
