import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QI

open Finset

/-! ### Classical entropies -/

/-- Shannon entropy of a probability vector, in nats. -/

lemma shannonEntropy_eq_neg_sum {α : Type*} [Fintype α] (f : α → ℝ) :
    shannonEntropy f = -∑ a, f a * Real.log (f a) := by
  simp only [shannonEntropy, Real.negMulLog_eq_neg, Finset.sum_neg_distrib]

/-! ### The log-sum inequality -/

/-- Pointwise ingredient of the log-sum inequality, obtained from `log x ≥ 1 - 1/x`. -/
