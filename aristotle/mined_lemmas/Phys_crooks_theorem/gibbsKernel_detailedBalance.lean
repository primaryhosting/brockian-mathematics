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

lemma gibbsKernel_detailedBalance (E : ℕ → X → ℝ) (beta : ℝ) :
    DetailedBalance E (gibbsKernel E beta) beta := by
  intro k a b
  simp only [gibbsKernel]
  ring

end Setup

section Proof

variable {X : Type*} [Fintype X] [Nonempty X]
variable {E : ℕ → X → ℝ} {T : ℕ → X → X → ℝ} {beta : ℝ} {N : ℕ} {x : ℕ → X}

omit [Fintype X] [Nonempty X] in
/-- The reversed product of kernels, reindexed. -/
