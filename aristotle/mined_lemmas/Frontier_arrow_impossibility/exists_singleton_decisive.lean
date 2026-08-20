import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

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

/-! ## Rankings (strict total orders) -/

/-- A *ranking* of the alternatives `A` is a strict total order: an irreflexive,
transitive and total (trichotomous) relation.  `r x y` means "`x` is strictly
preferred to `y`". -/
structure IsRanking {A : Type*} (r : A → A → Prop) : Prop where
  irrefl : ∀ x, ¬ r x x
  trans : ∀ {x y z}, r x y → r y z → r x z
  total : ∀ x y, x ≠ y → r x y ∨ r y x

namespace IsRanking

variable {A : Type*} {r : A → A → Prop}


theorem exists_singleton_decisive (hF : IsSWF F) (hU : Unanimity F) (hI : IIA F)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ (n : ℕ) (S : Finset V), S.card ≤ n → S.Nonempty →
      (∀ u v : A, u ≠ v → Decisive F S u v) →
      ∃ i : V, ∀ u v : A, u ≠ v → Decisive F ({i} : Finset V) u v := by
  intro n
  induction n with
  | zero =>
    intro S hcard hne _
    have := Finset.card_pos.mpr hne
    omega
  | succ n ih =>
    intro S hcard hne hdec
    by_cases h2 : 2 ≤ S.card
    · obtain ⟨i, hi⟩ := hne
      have hcard' : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi
      have hne' : (S.erase i).Nonempty := by
        rw [← Finset.card_pos, hcard']; omega
      rcases almostDecisive_split hF hI hab hac hbc hi hdec with hL | hR
      · exact ⟨i, decisive_all_of_almostDecisive hF hU hI hab hac hbc hac hL⟩
      · refine ih (S.erase i) (by omega) hne'
          (decisive_all_of_almostDecisive hF hU hI hab hac hbc (Ne.symm hbc) hR)
    · obtain ⟨i, rfl⟩ : ∃ i : V, S = {i} := by
        refine Finset.card_eq_one.mp ?_
        have := Finset.card_pos.mpr hne
        omega
      exact ⟨i, hdec⟩

end GroupContraction

/-! ## Arrow's theorem -/

section Main

variable {F : (V → A → A → Prop) → (A → A → Prop)}

/-- **Arrow's theorem** (positive form): with finitely many voters, at least one voter, and
at least three alternatives, every social welfare function satisfying unanimity and
independence of irrelevant alternatives has a dictator. -/
