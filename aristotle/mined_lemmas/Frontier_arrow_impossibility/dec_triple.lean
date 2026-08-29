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


theorem dec_triple (hU : Unanimity f) (hIIA : IIA f) {S : Finset ι} {x y z : A}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (h : SemiDec f S x y) :
    Dec f S x y ∧ Dec f S y x ∧ Dec f S x z ∧ Dec f S z x ∧ Dec f S y z ∧ Dec f S z y := by
  have dxz : Dec f S x z := dec_of_semiDec_right f hU hIIA hxy hyz hxz h
  have dyz : Dec f S y z :=
    dec_of_semiDec_left f hU hIIA hxz hyz.symm hxy (semiDec_of_dec f dxz)
  have dyx : Dec f S y x :=
    dec_of_semiDec_right f hU hIIA hyz hxz.symm hxy.symm (semiDec_of_dec f dyz)
  have dzx : Dec f S z x :=
    dec_of_semiDec_left f hU hIIA hxy.symm hxz hyz (semiDec_of_dec f dyx)
  have dzy : Dec f S z y :=
    dec_of_semiDec_right f hU hIIA hxz.symm hxy hyz.symm (semiDec_of_dec f dzx)
  have dxy : Dec f S x y :=
    dec_of_semiDec_left f hU hIIA hyz.symm hxy.symm hxz.symm (semiDec_of_dec f dzy)
  exact ⟨dxy, dyx, dxz, dzx, dyz, dzy⟩

