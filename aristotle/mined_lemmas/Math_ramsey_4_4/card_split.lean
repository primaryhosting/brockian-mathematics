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

lemma card_split {G : SimpleGraph V} {s A B : Finset V} {v : V} (hv : v ∈ s)
    (hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u) (hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u) :
    A.card + B.card + 1 = s.card := by
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro u huA huB
    exact ((hB u).1 huB).2.2 ((hA u).1 huA).2
  have hunion : A ∪ B = s.erase v := by
    ext u
    simp only [Finset.mem_union, hA, hB, Finset.mem_erase, SimpleGraph.compl_adj]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h2.ne', h1⟩
      · exact ⟨fun h => h2 h.symm, h1⟩
    · rintro ⟨h1, h2⟩
      by_cases hadj : G.Adj v u
      · exact Or.inl ⟨h2, hadj⟩
      · exact Or.inr ⟨h2, fun h => h1 h.symm, hadj⟩
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem hv] at hc
  have h1 : 1 ≤ s.card := Finset.card_pos.2 ⟨v, hv⟩
  omega

