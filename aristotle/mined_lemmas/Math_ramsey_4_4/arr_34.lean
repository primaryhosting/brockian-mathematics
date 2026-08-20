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

lemma arr_34 {G : SimpleGraph V} {s : Finset V} (hs : 9 ≤ s.card) : Arr G s 3 4 := by
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  exact (arr_34_eq ht).mono hts

