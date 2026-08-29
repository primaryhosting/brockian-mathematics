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


theorem exists_singleton_allDec (hU : Unanimity f) (hIIA : IIA f) {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (n : ℕ) (S : Finset ι), S.card = n → S.Nonempty → AllDec f S →
      ∃ i : ι, AllDec f ({i} : Finset ι) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hne hdec
    rcases eq_or_lt_of_le (Finset.one_le_card.2 hne) with hone | htwo
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 hone.symm
      exact ⟨i, hi ▸ hdec⟩
    · obtain ⟨i, hiS⟩ := hne
      have hdisj : ∀ j, j ∈ ({i} : Finset ι) → j ∉ S.erase i := by
        intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        simp
      have hunion : ∀ j, j ∈ S ↔ j ∈ ({i} : Finset ι) ∨ j ∈ S.erase i := by
        intro j
        simp only [Finset.mem_singleton, Finset.mem_erase]
        by_cases hji : j = i
        · subst hji; simp [hiS]
        · simp [hji]
      rcases allDec_split f hU hIIA hab hac hbc hdisj hunion hdec with hL | hR
      · exact ⟨i, hL⟩
      · refine ih (S.erase i).card ?_ (S.erase i) rfl ?_ hR
        · rw [← hcard]; exact Finset.card_erase_lt_of_mem hiS
        · refine Finset.card_pos.1 ?_
          rw [Finset.card_erase_of_mem hiS]
          omega

