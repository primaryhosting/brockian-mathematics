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

lemma pw_insert_ground {p : ℝ} {s W : Finset α} {x : α} (hx : x ∉ s) (hW : W ⊆ s) :
    pw p (insert x s) W = pw p s W * (1 - p) := by
  have hxW : x ∉ W := fun h => hx (hW h)
  have h : (insert x s) \ W = insert x (s \ W) := by
    ext y; simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, hxW⟩
      · exact ⟨Or.inr h1, h2⟩
  rw [pw, pw, h, Finset.card_insert_of_notMem (by simp [hx])]
  ring

