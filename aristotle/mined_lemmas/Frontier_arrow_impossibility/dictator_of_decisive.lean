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


theorem dictator_of_decisive {F : SWF V A} (hU : Unanimity F) (hI : IIA F) {v : V} {a c : A}
    (hac : a ≠ c) (hac' : Decisive F v a c) {e₁ e₂ e₃ : A}
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) : Dictator F v := by
  have key : ∀ x y : A, x ≠ y → Decisive F v x y := by
    intro x y hxy
    obtain ⟨z, hza, hzx⟩ := exists_ne_two h12 h13 h23 a x
    have d1 : Decisive F v a z := decisive_right hU hI hac hac' hza
    have d2 : Decisive F v x z := decisive_left hU hI (Ne.symm hza) d1 (Ne.symm hzx)
    exact decisive_right hU hI (Ne.symm hzx) d2 (Ne.symm hxy)
  intro P x y hxy
  rcases eq_or_ne x y with rfl | hne
  · exact absurd hxy ((P v).rel_irrefl x)
  · exact key x y hne P hxy

/-! ## The pivotal voter -/

/-- The pivotal voter argument, for voters indexed by `Fin n`: given three distinct
alternatives `a`, `b`, `c`, some voter is decisive for the pair `(a, c)`. -/
