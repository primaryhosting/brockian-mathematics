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

theorem arrows_nine : Arrows 9 3 4 := by
  classical
  intro G
  by_contra hcon
  push_neg at hcon
  obtain ⟨hcl, hind⟩ := hcon
  have hcf : G.CliqueFree 3 := hcl
  -- No vertex has degree at least four.
  have hdeg_le : ∀ v, G.degree v ≤ 3 := by
    intro v
    by_contra hlt
    push_neg at hlt
    have h4 : 4 ≤ (G.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree]; omega
    obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq h4
    refine hind T ⟨?_, hTcard⟩
    refine Set.Pairwise.mono ?_ (G.isIndepSet_neighborSet_of_triangleFree hcf v)
    intro x hx
    exact (mem_neighborFinset _ _ _).mp (hT hx)
  -- No vertex has degree at most two.
  have hdeg_ge : ∀ v, 3 ≤ G.degree v := by
    intro v
    by_contra hlt
    push_neg at hlt
    set S : Finset (Fin 9) := Finset.univ \ insert v (G.neighborFinset v) with hSdef
    have hins : (insert v (G.neighborFinset v)).card ≤ 3 := by
      have h1 := Finset.card_insert_le v (G.neighborFinset v)
      rw [card_neighborFinset_eq_degree] at h1
      omega
    have hScard : 6 ≤ S.card := by
      have h3 : S.card = 9 - (insert v (G.neighborFinset v)).card := by
        rw [hSdef, Finset.card_univ_diff]
        simp
      omega
    obtain ⟨T, hTS, hT3⟩ := exists_isNIndepSet_three G hcl S hScard
    have hvT : v ∉ T := by
      intro hv
      have := hTS hv
      rw [hSdef, Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_insert_self _ _)
    have hadj : ∀ t ∈ T, ¬ G.Adj v t := by
      intro t ht hadj
      have := hTS ht
      rw [hSdef, Finset.mem_sdiff] at this
      exact this.2 (Finset.mem_insert_of_mem ((mem_neighborFinset _ _ _).mpr hadj))
    exact hind _ (isNIndepSet_insert hvT hadj hT3)
  -- Hence `G` is 3-regular on 9 vertices, contradicting the handshake lemma.
  have hreg : ∀ v, G.degree v = 3 := fun v => le_antisymm (hdeg_le v) (hdeg_ge v)
  have hsum := G.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl (fun v _ => hreg v)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-! ### The lower bound: the Wagner graph on eight vertices -/

/-- The circulant graph `C₈(1,4)` (the Wagner graph): it is triangle-free and has
independence number three. -/
