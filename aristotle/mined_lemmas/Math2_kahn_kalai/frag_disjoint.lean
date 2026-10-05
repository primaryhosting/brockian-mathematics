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

lemma frag_disjoint {W S : Finset α} (hS : S ∈ H) : Disjoint (frag H W S) W := by
  obtain ⟨S', _, _, heq⟩ := frag_spec H hS
  rw [heq]
  exact Finset.sdiff_disjoint

/-- The sub-hypergraph of `H` consisting of the (large) fragments that we pay for. -/
