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

def RamseyProp (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 4

/-! ### Upper bound : every graph on 9 vertices has a triangle or an independent 4-set -/

section Upper

variable {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj]
  (h3 : G.CliqueFree 3) (h4 : Gᶜ.CliqueFree 4)

omit [DecidableRel G.Adj] in
include h3 in
/-- Triangle-freeness in element form. -/
