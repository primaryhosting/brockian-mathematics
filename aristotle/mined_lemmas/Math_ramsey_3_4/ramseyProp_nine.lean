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

theorem ramseyProp_nine : RamseyProp 9 := by
  intro G
  classical
  by_contra hcon
  push_neg at hcon
  exact no_good_graph_nine hcon.1 hcon.2

/-! ### Lower bound : the circulant graph `C₈(1,4)` on 8 vertices -/

/-- The relation generating the circulant graph `C₈(1,4)` (the Wagner graph). -/
