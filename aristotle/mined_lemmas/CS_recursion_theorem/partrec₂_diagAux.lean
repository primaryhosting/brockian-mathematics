/-
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

open Encodable Nat.Partrec Nat.Partrec.Code

/-- The diagonal helper used in Kleene's argument: on input `(x, y)` it runs the program
coded by `x` on input `x`, and then runs the program whose code is the resulting output
on input `y`.  This is a partial recursive function of two arguments. -/

theorem partrec₂_diagAux : Partrec₂ diagAux :=
  (eval_part.comp ((Computable.ofNat _).comp Computable.fst) Computable.fst).bind
    (eval_part.comp ((Computable.ofNat _).comp Computable.snd)
      (Computable.snd.comp Computable.fst)).to₂

/-- **Kleene's recursion theorem** (Rogers' fixed point form): every computable
transformation `f` of programs has a fixed point, i.e. a program `c` such that `c` and
`f c` compute exactly the same partial function. -/
