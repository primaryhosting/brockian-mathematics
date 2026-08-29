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


theorem allDec_split (hU : Unanimity f) (hIIA : IIA f) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) {S S₁ S₂ : Finset ι}
    (hdisj : ∀ i, i ∈ S₁ → i ∉ S₂) (hunion : ∀ i, i ∈ S ↔ i ∈ S₁ ∨ i ∈ S₂)
    (hS : AllDec f S) : AllDec f S₁ ∨ AllDec f S₂ := by
  obtain ⟨P, hP⟩ : ∃ P : ι → StrictPref A, ∀ i,
      P i = if i ∈ S₁ then pref3 a b c else if i ∈ S₂ then pref3 c a b else pref3 b c a :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∀ i, i ∈ S₁ → P i = pref3 a b c := by
    intro i hi; rw [hP i, if_pos hi]
  have e1 : ∀ i, i ∉ S₁ → i ∈ S₂ → P i = pref3 c a b := by
    intro i hi hj; rw [hP i, if_neg hi, if_pos hj]
  have e2 : ∀ i, i ∉ S₁ → i ∉ S₂ → P i = pref3 b c a := by
    intro i hi hj; rw [hP i, if_neg hi, if_neg hj]
  have h1 := pref3_lt hab hbc hac
  have h2 := pref3_lt (Ne.symm hac) hab (Ne.symm hbc)
  have h3 := pref3_lt hbc (Ne.symm hac) (Ne.symm hab)
  have hsoc : (f P).lt a b := by
    refine hS a b hab P (fun i hi => ?_)
    by_cases hi1 : i ∈ S₁
    · rw [e0 i hi1]; exact h1.1
    · rcases (hunion i).1 hi with hi' | hi2
      · exact absurd hi' hi1
      · rw [e1 i hi1 hi2]; exact h2.2.1
  rcases (f P).trichotomous' a c with hlt | heq | hgt
  · left
    refine allDec_of_semiDec f hU hIIA hab hac hbc hac ?_
    intro R hR1 hR2
    refine (hIIA P R a c (fun i => ?_)).1 hlt
    by_cases hi1 : i ∈ S₁
    · rw [e0 i hi1]; exact iff_of_true h1.2.2 (hR1 i hi1)
    · have hRi : ¬ (R i).lt a c := (R i).asymm (hR2 i hi1)
      by_cases hi2 : i ∈ S₂
      · rw [e1 i hi1 hi2]; exact iff_of_false ((pref3 c a b).asymm h2.1) hRi
      · rw [e2 i hi1 hi2]; exact iff_of_false ((pref3 b c a).asymm h3.2.1) hRi
  · exact absurd heq hac
  · right
    have hcb : (f P).lt c b := (f P).trans' hgt hsoc
    refine allDec_of_semiDec f hU hIIA hab hac hbc (Ne.symm hbc) ?_
    intro R hR1 hR2
    refine (hIIA P R c b (fun i => ?_)).1 hcb
    by_cases hi2 : i ∈ S₂
    · have hi1 : i ∉ S₁ := fun hx => hdisj i hx hi2
      rw [e1 i hi1 hi2]; exact iff_of_true h2.2.2 (hR1 i hi2)
    · have hRi : ¬ (R i).lt c b := (R i).asymm (hR2 i hi2)
      by_cases hi1 : i ∈ S₁
      · rw [e0 i hi1]; exact iff_of_false ((pref3 a b c).asymm h1.2.1) hRi
      · rw [e2 i hi1 hi2]; exact iff_of_false ((pref3 b c a).asymm h3.1) hRi

