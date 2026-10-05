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


theorem allDec_of_semiDec (hU : Unanimity f) (hIIA : IIA f) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {S : Finset ι} {u v : A} (huv : u ≠ v)
    (h : SemiDec f S u v) : AllDec f S := by
  have six : ∀ z : A, z ≠ u → z ≠ v →
      Dec f S u v ∧ Dec f S v u ∧ Dec f S u z ∧ Dec f S z u ∧ Dec f S v z ∧ Dec f S z v :=
    fun z hzu hzv => dec_triple f hU hIIA huv (Ne.symm hzv) (Ne.symm hzu) h
  obtain ⟨r, hru, hrv⟩ := exists_third hab hac hbc u v
  intro p q hpq
  by_cases hpu : p = u
  · subst hpu
    by_cases hqv : q = v
    · subst hqv; exact (six r hru hrv).1
    · exact (six q (Ne.symm hpq) hqv).2.2.1
  · by_cases hpv : p = v
    · subst hpv
      by_cases hqu : q = u
      · subst hqu; exact (six r hru hrv).2.1
      · exact (six q hqu (Ne.symm hpq)).2.2.2.2.1
    · by_cases hqu : q = u
      · subst hqu; exact (six p hpu hpv).2.2.2.1
      · by_cases hqv : q = v
        · subst hqv; exact (six p hpu hpv).2.2.2.2.2
        · exact dec_of_semiDec_right f hU hIIA hpu (Ne.symm hqu) hpq
            (semiDec_of_dec f (six p hpu hpv).2.2.2.1)

/-- Group contraction: a decisive coalition split in two has a decisive half. -/
