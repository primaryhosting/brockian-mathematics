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

lemma cand_nonempty {W S : Finset α} (hS : S ∈ H) : (cand H W S).Nonempty := by
  refine ⟨S \ W, ?_⟩
  simp only [cand, Finset.mem_image, Finset.mem_filter]
  exact ⟨S, ⟨hS, Finset.subset_union_right⟩, rfl⟩

/-- A minimum `(S, W)`-fragment: a smallest set of the form `S' \ W` with `S' ∈ H`,
`S' ⊆ W ∪ S`. -/
