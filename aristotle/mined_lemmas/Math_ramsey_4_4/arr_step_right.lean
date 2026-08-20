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

lemma arr_step_right {G : SimpleGraph V} {s B : Finset V} {v : V} (hv : v ∈ s) {p q : ℕ}
    (hB : ∀ u, u ∈ B ↔ u ∈ s ∧ Gᶜ.Adj v u) (h : Arr G B p (q)) : Arr G s p (q + 1) := by
  rw [← arr_compl]
  refine arr_step_left hv (A := B) ?_ ?_
  · intro u
    simpa using hB u
  · rw [arr_compl]
    exact h

