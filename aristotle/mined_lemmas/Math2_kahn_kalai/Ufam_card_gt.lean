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

lemma Ufam_card_gt {h : ℕ} {W : Finset α} : ∀ T ∈ Ufam H h W, h < T.card := by
  intro T hT
  obtain ⟨S, _, hc, heq⟩ := mem_Ufam_iff.1 hT
  exact heq ▸ hc

/-- Every edge of `H` contains its fragment, which lies in `Ufam ∪ Hfam`. -/
