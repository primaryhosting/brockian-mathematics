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

We define the two-colour Ramsey number `Math.ramseyNumber` and prove `R(3,4) = 9`.
-/

open Finset SimpleGraph

namespace Math

/-- `Arrows n r s` says that every simple graph on `n` vertices contains either a clique of
size `r` or an independent set of size `s`, i.e. `n → (r, s)` in Ramsey arrow notation. -/

theorem exists_isNIndepSet_three {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (h3 : ∀ A : Finset V, ¬ G.IsNClique 3 A) (S : Finset V) (hS : 6 ≤ S.card) :
    ∃ T ⊆ S, G.IsNIndepSet 3 T := by
  classical
  obtain ⟨u, hu⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcard : 5 ≤ (S.erase u).card := by
    rw [Finset.card_erase_of_mem hu]; omega
  set N := (S.erase u).filter (fun x => G.Adj u x) with hNdef
  set M := (S.erase u).filter (fun x => ¬ G.Adj u x) with hMdef
  have hsplit : N.card + M.card = (S.erase u).card :=
    Finset.card_filter_add_card_filter_not _
  by_cases hN3 : 3 ≤ N.card
  · obtain ⟨T, hTN, hTcard⟩ := Finset.exists_subset_card_eq hN3
    have hTS : T ⊆ S := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_filter x (hTN hx))
    refine ⟨T, hTS, ?_, hTcard⟩
    intro x hx y hy hxy hadj
    have hux : G.Adj u x := (Finset.mem_filter.mp (hTN hx)).2
    have huy : G.Adj u y := (Finset.mem_filter.mp (hTN hy)).2
    exact h3 {u, x, y} (is3Clique_triple_iff.mpr ⟨hux, huy, hadj⟩)
  · have hM3 : 3 ≤ M.card := by omega
    obtain ⟨T, hTM, hTcard⟩ := Finset.exists_subset_card_eq hM3
    have hTS : T ⊆ S := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_filter x (hTM hx))
    by_cases hclq : G.IsClique (T : Set V)
    · exact absurd ⟨hclq, hTcard⟩ (h3 T)
    · rw [SimpleGraph.isClique_iff, Set.Pairwise] at hclq
      push_neg at hclq
      obtain ⟨x, hx, y, hy, hxy, hnadj⟩ := hclq
      have hxT : x ∈ T := hx
      have hyT : y ∈ T := hy
      have hux : ¬ G.Adj u x := (Finset.mem_filter.mp (hTM hxT)).2
      have huy : ¬ G.Adj u y := (Finset.mem_filter.mp (hTM hyT)).2
      have hxu : x ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_filter x (hTM hxT))
      have hyu : y ≠ u := Finset.ne_of_mem_erase (Finset.mem_of_mem_filter y (hTM hyT))
      refine ⟨{u, x, y}, ?_, isNIndepSet_triple (Ne.symm hxu) (Ne.symm hyu) hxy hux huy hnadj⟩
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hu
      · exact hTS hxT
      · exact hTS hyT

/-! ### The upper bound: `9 → (3, 4)` -/

