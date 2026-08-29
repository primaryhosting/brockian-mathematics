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


theorem semiDec_of_dec {S : Finset ι} {x y : A} (h : Dec f S x y) : SemiDec f S x y :=
  fun P hP _ => h P hP

/-- Field expansion, first form: semi-decisiveness over `(x,y)` spreads to full
decisiveness over `(x,z)`. -/
