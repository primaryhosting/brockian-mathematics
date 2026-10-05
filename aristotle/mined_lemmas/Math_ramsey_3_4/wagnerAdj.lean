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

def wagnerAdj (a b : Fin 8) : Prop :=
  (a.val + 8 - b.val) % 8 = 1 ∨ (a.val + 8 - b.val) % 8 = 4 ∨ (a.val + 8 - b.val) % 8 = 7

instance : DecidableRel wagnerAdj := fun a b => by unfold wagnerAdj; infer_instance

/-- The Wagner graph: the cycle on 8 vertices together with its four main diagonals.
It is triangle-free and has independence number 3. -/
