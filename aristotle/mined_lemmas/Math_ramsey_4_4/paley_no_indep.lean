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

lemma paley_no_indep {a b c d : ℕ} (ha : a < 17) (hb : b < a) (hc : c < b) (hd : d < c)
    (h1 : paleyAdj a b = false) (h2 : paleyAdj a c = false) (h3 : paleyAdj a d = false)
    (h4 : paleyAdj b c = false) (h5 : paleyAdj b d = false) (h6 : paleyAdj c d = false) :
    False := by
  have h := paley_all ha hb hc hd
  simp [h1, h2, h3, h4, h5, h6] at h

