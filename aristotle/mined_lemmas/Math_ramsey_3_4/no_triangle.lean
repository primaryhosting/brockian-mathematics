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

theorem no_triangle {a b c : Fin 9} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    False :=
  h3 {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

omit [DecidableRel G.Adj] in
include h4 in
/-- No independent set of size four, in element form. -/
