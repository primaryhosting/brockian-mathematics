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

def r8 (a b : Fin 8) : Prop := (a.val + 1) % 8 = b.val ∨ (a.val + 4) % 8 = b.val

instance : DecidableRel r8 := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The Wagner graph: the circulant graph on 8 vertices with connection set `{±1, 4}`.
It is triangle-free and has independence number 3. -/
