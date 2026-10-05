import Mathlib
/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- A (strict) ranking of three alternatives, given by an injective "rank" function:
`rank a < rank b` means that `a` is strictly preferred to `b`. -/
structure Ranking where
  rank : Fin 3 → Fin 3
  rank_inj : Function.Injective rank

/-- `Prefers r a b` : the ranking `r` strictly prefers `a` to `b`. -/

lemma decisive_all {F : (Fin 2 → Ranking) → Ranking} (hU : Unanimous F) (hI : IIA F)
    {i : Fin 2} {a b : Fin 3} (hab : a ≠ b) (h : Decisive F i a b) :
    ∀ x y : Fin 3, x ≠ y → Decisive F i x y := by
  obtain ⟨c, hac, hbc⟩ := exists_third hab
  have dac : Decisive F i a c := decisive_right hU hI hab hac hbc h
  have dcb : Decisive F i c b := decisive_left hU hI hab hac hbc h
  have dbc : Decisive F i b c := decisive_left hU hI hac hab (Ne.symm hbc) dac
  have dca : Decisive F i c a := decisive_right hU hI (Ne.symm hbc) (Ne.symm hac) (Ne.symm hab) dcb
  have dba : Decisive F i b a := decisive_right hU hI hbc (Ne.symm hab) (Ne.symm hac) dbc
  have hmem : ∀ z : Fin 3, z = a ∨ z = b ∨ z = c := by
    have key : ∀ x u v w : Fin 3, u ≠ v → u ≠ w → v ≠ w → (x = u ∨ x = v ∨ x = w) := by decide
    exact fun z => key z a b c hab hac hbc
  intro x y hxy
  rcases hmem x with hx | hx | hx <;> rcases hmem y with hy | hy | hy <;>
    subst hx <;> subst hy <;>
      first
        | exact absurd rfl hxy
        | assumption

/-- A voter decisive on every pair is a dictator. -/
