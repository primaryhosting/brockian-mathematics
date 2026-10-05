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

lemma isSmall_minimalElts_iff {q : ℝ} {F : Finset (Finset α)} :
    IsSmall q (minimalElts F) ↔ IsSmall q F := by
  constructor
  · rintro ⟨G, hG, hc⟩; exact ⟨G, covers_minimalElts_iff.1 hG, hc⟩
  · rintro ⟨G, hG, hc⟩; exact ⟨G, covers_minimalElts_iff.2 hG, hc⟩

