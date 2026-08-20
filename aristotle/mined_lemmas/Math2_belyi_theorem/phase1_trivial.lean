import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma phase1_trivial (S : Finset ℂ) (hint : ∀ β ∈ S, IsIntegral ℚ β) (h : ∀ β ∈ S, deg β ≤ 1) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧ (∀ β ∈ S, IsRatPt (aeval β f)) ∧
      (∀ c : ℂ, aeval c (derivative f) = 0 → IsRatPt (aeval c f)) := by
  refine ⟨X, by simp, fun β hβ => ?_, fun c hc => ?_⟩
  · simpa using isRatPt_of_deg_le_one (hint β hβ) (h β hβ)
  · simp at hc

/-- Belyi's first reduction: for any finite set `S` of algebraic numbers there is a
rational polynomial `f` mapping `S` into `ℚ` and having all its critical values in `ℚ`. -/
