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

lemma partitionFn_pos (E : ℕ → X → ℝ) (beta : ℝ) (k : ℕ) : 0 < partitionFn E beta k := by
  refine Finset.sum_pos (fun x _ => Real.exp_pos _) ?_
  exact Finset.univ_nonempty

/-- Work performed on the system along the trajectory `x` during the protocol
`E 0, E 1, …, E N`: at step `k` the energy function is switched from `E k` to `E (k+1)`
while the system sits in state `x k`. -/
