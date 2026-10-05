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

lemma covers_union {h : ℕ} {W : Finset α} {G : Finset (Finset α)}
    (hG : Covers G (Hfam H h W)) : Covers (Ufam H h W ∪ G) H := by
  intro S hS
  by_cases hc : h < (frag H W S).card
  · exact ⟨frag H W S, Finset.mem_union_left _ (mem_Ufam_iff.2 ⟨S, hS, hc, rfl⟩),
      frag_subset H hS⟩
  · push_neg at hc
    obtain ⟨T, hT, hTsub⟩ := hG (frag H W S) (mem_Hfam_iff.2 ⟨S, hS, hc, rfl⟩)
    exact ⟨T, Finset.mem_union_right _ hT, hTsub.trans (frag_subset H hS)⟩

/-- Fragments are of the form `S' \ W`, so the residual family covers `Hfam`. -/
