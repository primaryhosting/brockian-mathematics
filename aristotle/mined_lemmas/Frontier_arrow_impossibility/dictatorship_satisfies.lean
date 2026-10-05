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


theorem dictatorship_satisfies (v₀ : V) :
    Unanimity (fun P : V → Ranking A => P v₀) ∧ IIA (fun P : V → Ranking A => P v₀) ∧
      Dictator (fun P : V → Ranking A => P v₀) v₀ :=
  ⟨fun _ _ _ h => h v₀, fun _ _ _ _ h => h v₀, fun _ _ _ h => h⟩

/-- Dropping unanimity, the remaining conditions are satisfiable when there are at least two
alternatives: the constant rule (always output a fixed ranking `R₀`) satisfies IIA and has no
dictator. -/
