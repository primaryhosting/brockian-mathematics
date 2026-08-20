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

theorem degree_le_three (v : Fin 9) : G.degree v ≤ 3 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := 4) (s := G.neighborFinset v) hlt
  refine h4 t ⟨?_, htc⟩
  intro x hx y hy hxy
  refine ⟨hxy, fun hadj => ?_⟩
  have hvx : G.Adj v x := by
    simpa using hts (by simpa using hx)
  have hvy : G.Adj v y := by
    simpa using hts (by simpa using hy)
  exact no_triangle h3 hvx hvy hadj

include h3 h4 in
/-- In a triangle-free graph on 9 vertices with no independent 4-set, every degree is at least 3. -/
