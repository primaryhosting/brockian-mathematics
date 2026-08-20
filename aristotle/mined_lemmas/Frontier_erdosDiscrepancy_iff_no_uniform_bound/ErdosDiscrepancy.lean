import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/

def ErdosDiscrepancy : Prop :=
  ∀ f : ℕ → ℤ, IsPlusMinusOne f → ∀ C : ℤ, ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ C < |apSum f d n|

/-- Reduction: the Erdős discrepancy statement is equivalent to saying that no `±1`
sequence admits a uniform bound on its discrepancy over homogeneous APs. -/
