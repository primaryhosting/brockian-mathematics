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

lemma exists_four_sorted {s : Finset (Fin 17)} (hs : s.card = 4) :
    ∃ a b c d : Fin 17, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ d ∈ s ∧
      d.val < c.val ∧ c.val < b.val ∧ b.val < a.val := by
  set e := s.orderIsoOfFin hs with he
  have key : ∀ i j : Fin 4, i < j → ((e i : Fin 17)).val < ((e j : Fin 17)).val := by
    intro i j hij
    exact e.lt_iff_lt.2 hij
  exact ⟨e 3, e 2, e 1, e 0, (e 3).2, (e 2).2, (e 1).2, (e 0).2,
    key 0 1 (by decide), key 1 2 (by decide), key 2 3 (by decide)⟩

