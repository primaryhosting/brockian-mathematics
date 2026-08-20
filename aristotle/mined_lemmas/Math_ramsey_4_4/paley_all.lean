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

lemma paley_all {a b c d : ℕ} (ha : a < 17) (hb : b < a) (hc : c < b) (hd : d < c) :
    (!(paleyAdj a b && paleyAdj a c && paleyAdj a d && paleyAdj b c && paleyAdj b d &&
          paleyAdj c d) &&
      !(!paleyAdj a b && !paleyAdj a c && !paleyAdj a d && !paleyAdj b c && !paleyAdj b d &&
          !paleyAdj c d)) = true := by
  have h := paleyCheck_eq
  rw [paleyCheck, List.all_eq_true] at h
  have h1 := h a (List.mem_range.2 ha)
  rw [List.all_eq_true] at h1
  have h2 := h1 b (List.mem_range.2 hb)
  rw [List.all_eq_true] at h2
  have h3 := h2 c (List.mem_range.2 hc)
  rw [List.all_eq_true] at h3
  exact h3 d (List.mem_range.2 hd)

