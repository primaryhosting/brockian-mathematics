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

noncomputable def forwardProb (E : ℕ → X → ℝ) (T : ℕ → X → X → ℝ) (beta : ℝ) (N : ℕ)
    (x : ℕ → X) : ℝ :=
  Real.exp (-beta * E 0 (x 0)) / partitionFn E beta 0 *
    ∏ k ∈ Finset.range N, T k (x k) (x (k + 1))

/-- Probability weight of a trajectory `y` under the time-reversed protocol: equilibrium initial
condition at `E N`, and the kernels applied in reverse order. -/
