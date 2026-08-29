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

lemma frag_exists_edge {W S : Finset α} (hS : S ∈ H) : ∃ R ∈ H, R ⊆ W ∪ frag H W S := by
  obtain ⟨S', hS', _, heq⟩ := frag_spec H (W := W) hS
  refine ⟨S', hS', fun y hy => ?_⟩
  by_cases hyW : y ∈ W
  · exact Finset.mem_union_left _ hyW
  · refine Finset.mem_union_right _ ?_
    rw [heq]
    exact Finset.mem_sdiff.2 ⟨hy, hyW⟩

/-- The key property (16) of Park–Pham: the minimum fragment `T` is contained in the
canonical edge chosen inside `Z = W ∪ T`. -/
