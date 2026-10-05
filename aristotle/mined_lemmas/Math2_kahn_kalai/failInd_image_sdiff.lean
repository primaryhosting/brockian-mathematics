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

lemma failInd_image_sdiff (H : Finset (Finset α)) (W V : Finset α) :
    failInd (H.image (fun S => S \ W)) V = failInd H (W ∪ V) := by
  unfold failInd
  congr 1
  apply propext
  constructor
  · rintro ⟨S, hS, hSV⟩
    obtain ⟨S₀, hS₀, rfl⟩ := Finset.mem_image.1 hS
    refine ⟨S₀, hS₀, fun y hy => ?_⟩
    by_cases hyW : y ∈ W
    · exact Finset.mem_union_left _ hyW
    · exact Finset.mem_union_right _ (hSV (Finset.mem_sdiff.2 ⟨hy, hyW⟩))
  · rintro ⟨S, hS, hSV⟩
    refine ⟨S \ W, Finset.mem_image.2 ⟨S, hS, rfl⟩, fun y hy => ?_⟩
    obtain ⟨hy1, hy2⟩ := Finset.mem_sdiff.1 hy
    rcases Finset.mem_union.1 (hSV hy1) with h | h
    · exact absurd h hy2
    · exact h

