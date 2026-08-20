import Mathlib
open Finset
namespace C4.Comb5


theorem inclusion_exclusion_three {α : Type*} [DecidableEq α] (A B C : Finset α) :
    (A ∪ B ∪ C).card = A.card + B.card + C.card - (A∩B).card - (A∩C).card - (B∩C).card + (A∩B∩C).card := by
  have hAB : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hABC : ((A ∪ B) ∪ C).card + ((A ∪ B) ∩ C).card = (A ∪ B).card + C.card :=
    Finset.card_union_add_card_inter (A ∪ B) C
  have hdist : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := Finset.union_inter_distrib_right A B C
  have hmid : ((A ∩ C) ∪ (B ∩ C)).card + ((A ∩ C) ∩ (B ∩ C)).card
      = (A ∩ C).card + (B ∩ C).card :=
    Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  have hcap : (A ∩ C) ∩ (B ∩ C) = A ∩ B ∩ C := by
    ext x; simp only [Finset.mem_inter]; tauto
  have hsub : (A ∩ B ∩ C).card ≤ (A ∪ B ∪ C).card := by
    refine Finset.card_le_card ?_
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_union] at *
    tauto
  rw [hcap] at hmid
  rw [hdist] at hABC
  omega

