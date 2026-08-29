import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma weight_zero (U : Finset α) : weight (0 : ℝ) U = if U = ∅ then 1 else 0 := by
  rw [weight_def]
  by_cases hU : U = ∅
  · subst hU; simp
  · have : U.card ≠ 0 := fun h => hU (Finset.card_eq_zero.1 h)
    rw [if_neg hU, zero_pow this, zero_mul]

/-- The `k`-round process is the same as a single round with the union parameter. -/
