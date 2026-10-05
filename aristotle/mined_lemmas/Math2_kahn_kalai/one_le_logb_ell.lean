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

lemma one_le_logb_ell (F : Finset (Finset α)) : 1 ≤ Real.logb 2 (ell F) := by
  have h2 : (2:ℝ) ≤ (ell F : ℝ) := by
    have : 2 ≤ ell F := le_max_left _ _
    exact_mod_cast this
  calc (1:ℝ) = Real.logb 2 2 := by simp
    _ ≤ Real.logb 2 (ell F) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2

