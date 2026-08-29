import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Rankings -/

/-- A strict linear ranking (irreflexive, transitive, total) of the alternatives `A`.
`R.rel a b` means "`a` is strictly preferred to `b`". -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {a b c : A}, rel a b → rel b c → rel a c
  rel_irrefl : ∀ a : A, ¬ rel a a
  rel_total : ∀ a b : A, a ≠ b → rel a b ∨ rel b a

namespace Ranking

variable {A : Type*}


theorem scoreRanking_not_rel {A : Type*} {s : A → ℕ} {x y : A} (h : s y < s x) :
    ¬ (scoreRanking s).rel x y := by
  rintro (h' | ⟨h', -⟩) <;> omega

/-! ## Social welfare functions and Arrow's conditions -/

/-- A social welfare function: it aggregates a profile of individual rankings (one per voter
in `V`) into a single social ranking of the alternatives `A`. -/
abbrev SWF (V A : Type*) := (V → Ranking A) → Ranking A

variable {A V : Type*}

/-- Unanimity (the weak Pareto condition): if every voter strictly prefers `a` to `b`,
so does society. -/
