import Mathlib
namespace MS2.CSLogic

/-- Cantor's diagonal argument: no map `α → (α → Bool)` is surjective. -/

theorem finite_no_surj_to_larger {A B : Type*} [Fintype A] [Fintype B]
    (h : Fintype.card A < Fintype.card B) (f : A → B) : ¬ Function.Surjective f := by
  intro hf
  exact absurd (Fintype.card_le_of_surjective f hf) (not_le.mpr h)

end MS2.CSLogic

