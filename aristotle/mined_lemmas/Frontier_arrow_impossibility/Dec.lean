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


def Dec (S : Finset ι) (x y : A) : Prop :=
  ∀ P : ι → StrictPref A, (∀ i ∈ S, (P i).lt x y) → (f P).lt x y

/-- The coalition `S` is semi-decisive for the ordered pair `(x, y)`: whenever all members
of `S` prefer `x` to `y` and all non-members prefer `y` to `x`, society prefers `x` to `y`. -/
