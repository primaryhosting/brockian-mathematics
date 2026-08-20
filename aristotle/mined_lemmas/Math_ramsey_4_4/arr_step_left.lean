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

lemma arr_step_left {G : SimpleGraph V} {s A : Finset V} {v : V} (hv : v ∈ s) {p q : ℕ}
    (hA : ∀ u, u ∈ A ↔ u ∈ s ∧ G.Adj v u) (h : Arr G A p q) : Arr G s (p + 1) q := by
  have hAs : A ⊆ s := fun u hu => ((hA u).1 hu).1
  rcases h with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
  · have hvt : v ∉ t := fun hvt => G.irrefl ((hA v).1 (hts hvt)).2
    refine Or.inl ⟨insert v t, ?_, ht.insert (fun b hb => ((hA b).1 (hts hb)).2)⟩
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hv
    · exact hAs (hts hx)
  · exact Or.inr ⟨t, hts.trans hAs, ht⟩

