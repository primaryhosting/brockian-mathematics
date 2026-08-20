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

lemma arr_two_left {G : SimpleGraph V} {s : Finset V} {q : ℕ} (hq : q ≤ s.card) :
    Arr G s 2 q := by
  by_cases hex : ∃ a ∈ s, ∃ b ∈ s, G.Adj a b
  · obtain ⟨a, ha, b, hb, hab⟩ := hex
    refine Or.inl ⟨{a, b}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · simp [SimpleGraph.isNClique_iff, SimpleGraph.isClique_iff, Set.pairwise_insert,
        hab, hab.symm, hab.ne]
  · push_neg at hex
    obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hq
    refine Or.inr ⟨t, hts, ?_⟩
    rw [SimpleGraph.isNClique_iff]
    refine ⟨?_, ht⟩
    intro x hx y hy hxy
    exact ⟨hxy, hex x (hts hx) y (hts hy)⟩

