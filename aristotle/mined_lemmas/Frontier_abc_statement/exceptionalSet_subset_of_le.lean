/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma exceptionalSet_subset_of_le {ε ε' : ℝ} (h : ε ≤ ε') :
    exceptionalSet ε' ⊆ exceptionalSet ε := by
  rintro ⟨a, b, c⟩ ⟨ht, hlt⟩
  refine ⟨ht, lt_of_le_of_lt ?_ hlt⟩
  exact Real.rpow_le_rpow_of_exponent_le (one_le_rad _) (by linarith)

/-- It suffices to prove the abc conjecture for arbitrarily small `ε`. -/
