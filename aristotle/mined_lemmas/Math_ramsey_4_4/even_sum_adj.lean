import Mathlib
/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

open scoped Classical

namespace Ramsey44

variable {V : Type*}

/-- `Arr G s p q` says that inside the vertex set `s` there is either a `p`-clique of `G`
or a `q`-clique of the complement of `G` (i.e. an independent set of size `q`). -/

lemma even_sum_adj (G : SimpleGraph V) (s : Finset V) :
    Even (∑ v ∈ s, (s.filter (fun u => G.Adj v u)).card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ((insert a t).filter (fun u => G.Adj a u)) = t.filter (fun u => G.Adj a u) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hu, h2⟩
        · exact absurd h2 (G.irrefl)
        · exact ⟨hu, h2⟩
      · rintro ⟨hu, h2⟩; exact ⟨Or.inr hu, h2⟩
    have h2 : ∀ v ∈ t, ((insert a t).filter (fun u => G.Adj v u)).card
        = (t.filter (fun u => G.Adj v u)).card + (if G.Adj v a then 1 else 0) := by
      intro v hv
      by_cases hva : G.Adj v a
      · have hins : ((insert a t).filter (fun u => G.Adj v u))
            = insert a (t.filter (fun u => G.Adj v u)) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hu, h3⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨hu, h3⟩
          · rintro (rfl | ⟨hu, h3⟩)
            · exact ⟨Or.inl rfl, hva⟩
            · exact ⟨Or.inr hu, h3⟩
        rw [hins, Finset.card_insert_of_notMem (by simp [ha]), if_pos hva]
      · have hins : ((insert a t).filter (fun u => G.Adj v u))
            = t.filter (fun u => G.Adj v u) := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hu, h3⟩
            · exact absurd h3 hva
            · exact ⟨hu, h3⟩
          · rintro ⟨hu, h3⟩; exact ⟨Or.inr hu, h3⟩
        rw [hins, if_neg hva, Nat.add_zero]
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, h1]
    have h3 : (∑ v ∈ t, if G.Adj v a then 1 else 0) = (t.filter (fun u => G.Adj a u)).card := by
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl fun x _ => by simp [SimpleGraph.adj_comm]
    rw [h3]
    rcases ih with ⟨k, hk⟩
    exact ⟨k + (t.filter (fun u => G.Adj a u)).card, by omega⟩

/-- `R(3,3) ≤ 6`. -/
