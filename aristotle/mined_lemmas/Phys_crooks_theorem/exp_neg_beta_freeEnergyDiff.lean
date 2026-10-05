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

lemma exp_neg_beta_freeEnergyDiff (E : ℕ → X → ℝ) (beta : ℝ) (N : ℕ) (hbeta : beta ≠ 0) :
    Real.exp (-beta * freeEnergyDiff E beta N)
      = partitionFn E beta N / partitionFn E beta 0 := by
  unfold freeEnergyDiff
  have h : -beta * (-(1 / beta) * Real.log (partitionFn E beta N / partitionFn E beta 0))
      = Real.log (partitionFn E beta N / partitionFn E beta 0) := by
    field_simp
  rw [h, Real.exp_log]
  exact div_pos (partitionFn_pos E beta N) (partitionFn_pos E beta 0)

/-- Detailed balance: after the work step `k` the kernel `T k` is in detailed balance with
respect to the (new) energy function `E (k+1)`. -/
