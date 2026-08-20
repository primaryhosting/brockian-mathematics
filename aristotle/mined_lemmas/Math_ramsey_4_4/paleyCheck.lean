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

def paleyCheck : Bool :=
  (List.range 17).all fun a => (List.range a).all fun b => (List.range b).all fun c =>
    (List.range c).all fun d =>
      !(paleyAdj a b && paleyAdj a c && paleyAdj a d && paleyAdj b c && paleyAdj b d &&
          paleyAdj c d) &&
      !(!paleyAdj a b && !paleyAdj a c && !paleyAdj a d && !paleyAdj b c && !paleyAdj b d &&
          !paleyAdj c d)

set_option maxRecDepth 100000 in
