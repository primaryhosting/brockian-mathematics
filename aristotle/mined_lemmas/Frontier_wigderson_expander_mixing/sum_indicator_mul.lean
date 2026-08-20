import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Frontier

section Aux

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- Cauchy–Schwarz for finite sums, in absolute-value / square-root form. -/

lemma sum_indicator_mul (S : Finset V) (g : V → ℝ) :
    ∑ x, (if x ∈ S then (1:ℝ) else 0) * g x = ∑ x ∈ S, g x := by
  rw [Finset.sum_congr rfl (fun x _ => by rw [ite_mul, one_mul, zero_mul])]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Summing against the indicator vector of a finset restricts the sum to that finset. -/
