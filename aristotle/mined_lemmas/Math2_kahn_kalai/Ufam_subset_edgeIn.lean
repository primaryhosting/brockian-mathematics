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

lemma Ufam_subset_edgeIn {h : ℕ} {W T : Finset α} (hT : T ∈ Ufam H h W) :
    T ⊆ edgeIn H (W ∪ T) := by
  obtain ⟨S, hS, _, heq⟩ := mem_Ufam_iff.1 hT
  rw [← heq]; exact frag_subset_edgeIn hS

end Fragment

end Math2

