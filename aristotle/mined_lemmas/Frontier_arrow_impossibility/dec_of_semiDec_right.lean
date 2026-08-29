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


theorem dec_of_semiDec_right (hU : Unanimity f) (hIIA : IIA f) {S : Finset ι} {x y z : A}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (h : SemiDec f S x y) : Dec f S x z := by
  intro Q hQ
  obtain ⟨P, hP⟩ : ∃ P : ι → StrictPref A, ∀ i,
      P i = if i ∈ S then pref3 x y z else if (Q i).lt x z then pref3 y x z else pref3 y z x :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∀ i, i ∈ S → P i = pref3 x y z := by
    intro i hi; rw [hP i, if_pos hi]
  have e1 : ∀ i, i ∉ S → (Q i).lt x z → P i = pref3 y x z := by
    intro i hi hc; rw [hP i, if_neg hi, if_pos hc]
  have e2 : ∀ i, i ∉ S → ¬ (Q i).lt x z → P i = pref3 y z x := by
    intro i hi hc; rw [hP i, if_neg hi, if_neg hc]
  have hs := pref3_lt hxy hyz hxz
  have ha := pref3_lt hxy.symm hxz hyz
  have hb := pref3_lt hyz hxz.symm hxy.symm
  have h1 : (f P).lt y z := by
    refine hU P y z (fun i => ?_)
    by_cases hi : i ∈ S
    · rw [e0 i hi]; exact hs.2.1
    · by_cases hc : (Q i).lt x z
      · rw [e1 i hi hc]; exact ha.2.2
      · rw [e2 i hi hc]; exact hb.1
  have h2 : (f P).lt x y := by
    refine h P (fun i hi => ?_) (fun i hi => ?_)
    · rw [e0 i hi]; exact hs.1
    · by_cases hc : (Q i).lt x z
      · rw [e1 i hi hc]; exact ha.1
      · rw [e2 i hi hc]; exact hb.2.2
  refine (hIIA P Q x z (fun i => ?_)).1 ((f P).trans' h2 h1)
  by_cases hi : i ∈ S
  · rw [e0 i hi]; exact iff_of_true hs.2.2 (hQ i hi)
  · by_cases hc : (Q i).lt x z
    · rw [e1 i hi hc]; exact iff_of_true ha.2.1 hc
    · rw [e2 i hi hc]; exact iff_of_false ((pref3 y z x).asymm hb.2.1) hc

/-- Field expansion, second form: semi-decisiveness over `(x,y)` spreads to full
decisiveness over `(z,y)`. -/
