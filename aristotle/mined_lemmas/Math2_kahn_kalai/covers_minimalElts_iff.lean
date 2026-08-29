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

lemma covers_minimalElts_iff {G F : Finset (Finset α)} :
    Covers G (minimalElts F) ↔ Covers G F := by
  constructor
  · intro h S hS
    obtain ⟨S₀, hS₀, hS₀S⟩ := exists_minimal_subset hS
    obtain ⟨T, hT, hTS₀⟩ := h S₀ hS₀
    exact ⟨T, hT, hTS₀.trans hS₀S⟩
  · intro h S hS
    exact h S (minimalElts_subset F hS)

