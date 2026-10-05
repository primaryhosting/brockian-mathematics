/-
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.Computability.PartrecCode

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Kleene's recursion theorem.** Every computable transformation `f` of programs
(here: of codes for partial recursive functions) has a fixed point *up to semantics*:
there is a code `c` whose behaviour is exactly that of the transformed code `f c`.

This is `Nat.Partrec.Code.fixed_point` in Mathlib. -/
theorem recursion_theorem {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  Code.fixed_point hf

/-- Parametrised form of the recursion theorem (Kleene's second recursion theorem):
for a partial recursive `f : Code → ℕ →. ℕ` there is a code `c` computing `f c`,
i.e. a program with access to its own source code.

This is `Nat.Partrec.Code.fixed_point₂` in Mathlib. -/
theorem recursion_theorem₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c :=
  Code.fixed_point₂ hf

end CS

import Mathlib

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

