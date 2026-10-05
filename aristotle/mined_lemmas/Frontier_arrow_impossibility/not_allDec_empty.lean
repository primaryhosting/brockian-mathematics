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


theorem not_allDec_empty {a b : A} (hab : a ≠ b)
    (h : AllDec f (∅ : Finset ι)) : False := by
  have P : ι → StrictPref A := fun _ => tierPref (fun _ => 0)
  have h1 := h a b hab P (by simp)
  have h2 := h b a (Ne.symm hab) P (by simp)
  exact (f P).asymm h1 h2

/-! ## Arrow's impossibility theorem -/

/-- **Arrow's impossibility theorem.** With finitely many voters and at least three
alternatives, no social welfare function satisfies unanimity, independence of irrelevant
alternatives, and non-dictatorship. -/
