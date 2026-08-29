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


theorem constant_rule_satisfies (R₀ : Ranking A) {p q : A} (hpq : p ≠ q) :
    IIA (fun _ : V → Ranking A => R₀) ∧ ∀ v : V, ¬ Dictator (fun _ : V → Ranking A => R₀) v := by
  refine ⟨fun _ _ _ _ _ => Iff.rfl, fun v hv => ?_⟩
  classical
  -- feed the rule a profile where `v` disagrees with `R₀`
  rcases R₀.rel_total p q hpq with h | h
  · obtain ⟨s, hs⟩ : ∃ s : A → ℕ, s = fun x => if x = q then 0 else 1 := ⟨_, rfl⟩
    have h1 : (scoreRanking s).rel q p := scoreRanking_rel (by simp [hs, hpq])
    exact R₀.asymm h (hv (fun _ => scoreRanking s) q p h1)
  · obtain ⟨s, hs⟩ : ∃ s : A → ℕ, s = fun x => if x = p then 0 else 1 := ⟨_, rfl⟩
    have h1 : (scoreRanking s).rel p q := scoreRanking_rel (by simp [hs, Ne.symm hpq])
    exact R₀.asymm h (hv (fun _ => scoreRanking s) p q h1)

/-- The base case: three alternatives and two voters.  No ranked voting rule for the three
alternatives `Fin 3` and the two voters `Fin 2` is unanimous, independent of irrelevant
alternatives and non-dictatorial. -/
