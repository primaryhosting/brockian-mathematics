/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

open Finset

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s` or an independent set (a clique in the complement) of size `t`. -/

lemma ramsey_3_3 (G : SimpleGraph V) (A : Finset V) (hA : 6 ≤ A.card) :
    (∃ S ⊆ A, ((S : Set V).Pairwise G.Adj) ∧ S.card = 3) ∨
    (∃ S ⊆ A, ((S : Set V).Pairwise fun a b => ¬ G.Adj a b) ∧ S.card = 3) := by
  classical
  obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_subset_card_eq hA
  have hne : A'.Nonempty := by rw [← Finset.card_pos, hA'card]; norm_num
  obtain ⟨v, hv⟩ := hne
  set B := A'.erase v with hB
  have hBA : B ⊆ A := fun x hx => hA'sub (Finset.mem_of_mem_erase hx)
  have hBcard : B.card = 5 := by rw [hB, Finset.card_erase_of_mem hv, hA'card]
  have hsplit : (B.filter (fun u => G.Adj v u)).card
      + (B.filter (fun u => ¬ G.Adj v u)).card = 5 := by
    rw [Finset.card_filter_add_card_filter_not, hBcard]
  have hcase : 3 ≤ (B.filter (fun u => G.Adj v u)).card
      ∨ 3 ≤ (B.filter (fun u => ¬ G.Adj v u)).card := by omega
  rcases hcase with hc | hc
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hc
    by_cases hp : ((S : Set V).Pairwise fun a b => ¬ G.Adj a b)
    · exact Or.inr ⟨S, fun x hx => hBA (Finset.mem_of_mem_filter x (hSsub hx)), hp, hScard⟩
    · left
      simp only [Set.Pairwise, not_forall, not_not] at hp
      obtain ⟨a, ha, b, hb, hab, hadj⟩ := hp
      have haF := hSsub ha
      have hbF := hSsub hb
      rw [Finset.mem_filter] at haF hbF
      have hva : v ≠ a := by rintro rfl; exact Finset.notMem_erase v A' haF.1
      have hvb : v ≠ b := by rintro rfl; exact Finset.notMem_erase v A' hbF.1
      refine ⟨{v, a, b}, ?_, ?_, card_triple v a b hva hvb hab⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl|rfl|rfl
        · exact hA'sub hv
        · exact hBA haF.1
        · exact hBA hbF.1
      · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
        exact pairwise_triple _ (fun _ _ h => G.symm h) v a b haF.2 hbF.2 hadj
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hc
    by_cases hp : ((S : Set V).Pairwise G.Adj)
    · exact Or.inl ⟨S, fun x hx => hBA (Finset.mem_of_mem_filter x (hSsub hx)), hp, hScard⟩
    · right
      simp only [Set.Pairwise, not_forall] at hp
      obtain ⟨a, ha, b, hb, hab, hadj⟩ := hp
      have haF := hSsub ha
      have hbF := hSsub hb
      rw [Finset.mem_filter] at haF hbF
      have hva : v ≠ a := by rintro rfl; exact Finset.notMem_erase v A' haF.1
      have hvb : v ≠ b := by rintro rfl; exact Finset.notMem_erase v A' hbF.1
      refine ⟨{v, a, b}, ?_, ?_, card_triple v a b hva hvb hab⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl|rfl|rfl
        · exact hA'sub hv
        · exact hBA haF.1
        · exact hBA hbF.1
      · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
        exact pairwise_triple _ (fun _ _ h hh => h (G.symm hh)) v a b haF.2 hbF.2 hadj

end R33

/-! ## R(3,4) ≤ 9 -/

section R34

/-- Every graph on nine vertices contains a triangle or an independent set of size four. -/
