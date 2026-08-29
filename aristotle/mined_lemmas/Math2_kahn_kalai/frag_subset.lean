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

lemma frag_subset {W S : Finset α} (hS : S ∈ H) : frag H W S ⊆ S := by
  obtain ⟨S', _, hsub, heq⟩ := frag_spec H hS
  rw [heq]
  intro y hy
  simp only [Finset.mem_sdiff] at hy
  rcases Finset.mem_union.1 (hsub hy.1) with h | h
  · exact absurd h hy.2
  · exact h

