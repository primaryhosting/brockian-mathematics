/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

open Finset

/-- `RamseyProp n` says that every simple graph on `n` vertices contains either a triangle
(a 3-clique) or an independent set of size 4 (a 4-clique in the complement). -/

theorem G8_compl_cliqueFree_four : G8ᶜ.CliqueFree 4 := by
  unfold SimpleGraph.CliqueFree; decide

/-- For `n ≤ 8`, the graph induced by the Wagner graph on the first `n` vertices witnesses
`¬ RamseyProp n`. -/
