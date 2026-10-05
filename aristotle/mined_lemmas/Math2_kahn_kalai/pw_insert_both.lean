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

lemma pw_insert_both {p : ℝ} {s W : Finset α} {x : α} (hx : x ∉ s) (hW : W ⊆ s) :
    pw p (insert x s) (insert x W) = pw p s W * p := by
  have hxW : x ∉ W := fun h => hx (hW h)
  have h1 : (insert x s) \ (insert x W) = s \ W := by
    ext y; simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact absurd h1 h2
      · exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      refine ⟨Or.inr h1, ?_, h2⟩
      rintro rfl; exact hx h1
  rw [pw, pw, h1, Finset.card_insert_of_notMem hxW]
  ring

/-- The union of two independent random subsets is again a random subset. -/
