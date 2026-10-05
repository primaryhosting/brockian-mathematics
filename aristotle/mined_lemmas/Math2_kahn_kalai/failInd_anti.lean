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

lemma failInd_anti {H : Finset (Finset α)} {U V : Finset α} (h : U ⊆ V) :
    failInd H V ≤ failInd H U := by
  unfold failInd
  split_ifs with hV hU hU'
  · exact le_rfl
  · norm_num
  · obtain ⟨S, hS, hSU⟩ := hU'
    exact absurd ⟨S, hS, hSU.trans h⟩ hV
  · exact le_rfl

/-- The probability that the random set `U` (each element present independently with
probability `p`) contains no edge of `H`. -/
