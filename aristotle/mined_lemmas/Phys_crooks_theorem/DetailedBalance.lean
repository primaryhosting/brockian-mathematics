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

def DetailedBalance (E : ℕ → X → ℝ) (T : ℕ → X → X → ℝ) (beta : ℝ) : Prop :=
  ∀ k a b, Real.exp (-beta * E (k + 1) a) * T k a b = Real.exp (-beta * E (k + 1) b) * T k b a

/-- The Gibbs (heat-bath) relaxation kernel for the energy function `E (k+1)`. -/
