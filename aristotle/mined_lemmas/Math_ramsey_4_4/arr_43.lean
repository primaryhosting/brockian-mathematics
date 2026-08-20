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

lemma arr_43 {G : SimpleGraph V} {s : Finset V} (hs : 9 ≤ s.card) : Arr G s 4 3 := by
  rw [← arr_compl]
  exact arr_34 hs

/-- `R(4,4) ≤ 18`. -/
