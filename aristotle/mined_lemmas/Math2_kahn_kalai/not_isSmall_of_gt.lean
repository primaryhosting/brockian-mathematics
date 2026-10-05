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

lemma not_isSmall_of_gt {F : Finset (Finset α)} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : expThreshold F < q) : ¬ IsSmall q F := by
  intro hs
  have : q ≤ expThreshold F := le_csSup ⟨1, fun x hx => hx.2.1⟩ ⟨hq0, hq1, hs⟩
  linarith

