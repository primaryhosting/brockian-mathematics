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

lemma univ_mem_of_nonempty {F : Finset (Finset α)} (hinc : Increasing F) (hne : F.Nonempty) :
    (Finset.univ : Finset α) ∈ F := by
  obtain ⟨A, hA⟩ := hne
  exact hinc A hA Finset.univ (Finset.subset_univ A)

