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


theorem decisive_all_of_almostDecisive (hF : IsSWF F) (hU : Unanimity F) (hI : IIA F)
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {S : Finset V} {x y : A} (hxy : x ≠ y) (h : AlmostDecisive F S x y) :
    ∀ u v : A, u ≠ v → Decisive F S u v := by
  classical
  -- pick a third alternative `t` distinct from `x` and `y`
  obtain ⟨t, htx, hty⟩ : ∃ t : A, t ≠ x ∧ t ≠ y := by
    rcases exists_avoiding hab hac hbc x y with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, h1, h2⟩
    · exact ⟨b, h1, h2⟩
    · exact ⟨c, h1, h2⟩
  -- all six ordered pairs from {x, y, t}
  have hxt : Decisive F S x t :=
    decisive_fst_of_almostDecisive hF hU hI hxy htx hty h
  have hDty : Decisive F S t y :=
    decisive_snd_of_almostDecisive hF hU hI hxy htx hty h
  have hyt : Decisive F S y t :=
    decisive_snd_of_almostDecisive hF hU hI (Ne.symm htx) (Ne.symm hxy) (Ne.symm hty)
      (AlmostDecisive.of_decisive hxt)
  have hyx : Decisive F S y x :=
    decisive_fst_of_almostDecisive hF hU hI (Ne.symm hty) hxy (Ne.symm htx)
      (AlmostDecisive.of_decisive hyt)
  have htx' : Decisive F S t x :=
    decisive_fst_of_almostDecisive hF hU hI hty (Ne.symm htx) hxy
      (AlmostDecisive.of_decisive hDty)
  have hxy' : Decisive F S x y :=
    decisive_snd_of_almostDecisive hF hU hI hty (Ne.symm htx) hxy
      (AlmostDecisive.of_decisive hDty)
  -- almost decisiveness for all ordered pairs from {x, y, t}
  have key : ∀ u v : A, (u = x ∨ u = y ∨ u = t) → (v = x ∨ v = y ∨ v = t) → u ≠ v →
      AlmostDecisive F S u v := by
    rintro u v (rfl | rfl | rfl) (rfl | rfl | rfl) hne
    · exact absurd rfl hne
    · exact AlmostDecisive.of_decisive hxy'
    · exact AlmostDecisive.of_decisive hxt
    · exact AlmostDecisive.of_decisive hyx
    · exact absurd rfl hne
    · exact AlmostDecisive.of_decisive hyt
    · exact AlmostDecisive.of_decisive htx'
    · exact AlmostDecisive.of_decisive hDty
    · exact absurd rfl hne
  intro u v huv
  -- pick a member `w` of {x, y, t} different from `u` and `v`
  obtain ⟨w, hw, hwu, hwv⟩ : ∃ w : A, (w = x ∨ w = y ∨ w = t) ∧ w ≠ u ∧ w ≠ v := by
    rcases exists_avoiding hxy (Ne.symm htx) (Ne.symm hty) u v with
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨x, Or.inl rfl, h1, h2⟩
    · exact ⟨y, Or.inr (Or.inl rfl), h1, h2⟩
    · exact ⟨t, Or.inr (Or.inr rfl), h1, h2⟩
  -- first show `S` is almost decisive for `(u, w)`
  have huw : AlmostDecisive F S u w := by
    by_cases hu : u = x ∨ u = y ∨ u = t
    · exact key u w hu hw (Ne.symm hwu)
    · -- `u` is outside {x, y, t}; pick some pair from {x, y, t} avoiding `u`
      push_neg at hu
      obtain ⟨hux, huy, hut⟩ := hu
      rcases hw with rfl | rfl | rfl
      · exact AlmostDecisive.of_decisive
          (decisive_snd_of_almostDecisive hF hU hI (Ne.symm hxy) huy hux
            (key y w (Or.inr (Or.inl rfl)) (Or.inl rfl) (Ne.symm hxy)))
      · exact AlmostDecisive.of_decisive
          (decisive_snd_of_almostDecisive hF hU hI hxy hux huy
            (key x w (Or.inl rfl) (Or.inr (Or.inl rfl)) hxy))
      · exact AlmostDecisive.of_decisive
          (decisive_snd_of_almostDecisive hF hU hI (Ne.symm htx) hux hut
            (key x w (Or.inl rfl) (Or.inr (Or.inr rfl)) (Ne.symm htx)))
  exact decisive_fst_of_almostDecisive hF hU hI (Ne.symm hwu) (Ne.symm huv) (Ne.symm hwv) huw

end FieldExpansion

/-! ## Group contraction -/

/-- Comparing two rankings that agree on the ordered pair `(x, y)`. -/
