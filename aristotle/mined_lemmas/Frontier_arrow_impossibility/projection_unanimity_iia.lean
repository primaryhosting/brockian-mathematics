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


theorem projection_unanimity_iia (i₀ : ι) :
    Unanimity (fun P : ι → StrictPref A => P i₀) ∧ IIA (fun P : ι → StrictPref A => P i₀) ∧
      Dictator (fun P : ι → StrictPref A => P i₀) i₀ :=
  ⟨fun _ _ _ h => h i₀, fun _ _ _ _ h => h i₀, fun _ _ _ h => h⟩

/-- Equivalent positive form: a unanimous social welfare function satisfying IIA over at
least three alternatives has a dictator. -/
