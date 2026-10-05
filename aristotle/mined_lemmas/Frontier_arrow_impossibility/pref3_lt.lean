/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- A strict preference relation on the set of alternatives `A`: a strict linear order,
given by a transitive, trichotomous, irreflexive relation. -/
structure StrictPref (A : Type*) where
  lt : A → A → Prop
  trans' : ∀ {x y z : A}, lt x y → lt y z → lt x z
  trichotomous' : ∀ x y : A, lt x y ∨ x = y ∨ lt y x
  irrefl' : ∀ x : A, ¬ lt x x

namespace StrictPref

variable {A : Type*}


theorem pref3_lt {x y z : A} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    (pref3 x y z).lt x y ∧ (pref3 x y z).lt y z ∧ (pref3 x y z).lt x z := by
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;>
    simp [hxy.symm, hyz.symm, hxz.symm]

/-! ## Decisive coalitions -/

variable (f : (ι → StrictPref A) → StrictPref A)

/-- The coalition `S` is decisive for the ordered pair `(x, y)`: whenever all members of `S`
prefer `x` to `y`, so does society (regardless of the other voters). -/
