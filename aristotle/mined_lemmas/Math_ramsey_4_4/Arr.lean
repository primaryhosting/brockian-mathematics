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

lemma Arr.mono {G : SimpleGraph V} {s s' : Finset V} {p q : ℕ} (hss : s ⊆ s')
    (h : Arr G s p q) : Arr G s' p q := by
  rcases h with ⟨t, hts, ht⟩ | ⟨t, hts, ht⟩
  · exact Or.inl ⟨t, hts.trans hss, ht⟩
  · exact Or.inr ⟨t, hts.trans hss, ht⟩

/-- `R(2,q) ≤ q`. -/
