/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Math

open SimpleGraph

/-- `RamseyProp n` says that every simple graph on `n` vertices contains either a triangle
(a clique of size `3`) or an independent set of size `4`. -/

theorem not_ramseyProp_eight : ¬ RamseyProp 8 := by
  intro h
  rcases h wagner with ⟨s, hs⟩ | ⟨t, ht⟩
  · exact wagner_no_triangle s hs
  · exact wagner_no_indep_four t ht

/-- **R(3,4) = 9**: nine is the least `n` such that every graph on `n` vertices contains a
triangle or an independent set of size four. -/
