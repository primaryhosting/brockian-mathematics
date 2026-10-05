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

lemma threshold_le_one {F : Finset (Finset α)} (hinc : Increasing F) (hne : F.Nonempty) :
    threshold F ≤ 1 := by
  refine threshold_le_of_mem zero_le_one le_rfl ?_
  rw [mu_one_of_univ_mem (univ_mem_of_nonempty hinc hne)]
  norm_num

