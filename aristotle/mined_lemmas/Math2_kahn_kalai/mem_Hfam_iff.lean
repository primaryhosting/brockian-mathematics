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

lemma mem_Hfam_iff {h : ℕ} {W T : Finset α} :
    T ∈ Hfam H h W ↔ ∃ S ∈ H, (frag H W S).card ≤ h ∧ frag H W S = T := by
  simp only [Hfam, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨S, ⟨hS, hc⟩, heq⟩; exact ⟨S, hS, hc, heq⟩
  · rintro ⟨S, hS, hc, heq⟩; exact ⟨S, ⟨hS, hc⟩, heq⟩

