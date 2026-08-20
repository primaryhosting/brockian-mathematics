/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Statement: Kleene's recursion theorem: every computable transformation of programs has a fixed point.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.Computability.PartrecCode
import Mathlib

/-
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Kleene's recursion (fixed point) theorem.**
Every computable transformation `f` of programs (codes for partial recursive functions)
has a fixed point up to semantics: there is a code `c` such that the program `f c`
computes exactly the same partial function as `c` itself.

This is exactly `Nat.Partrec.Code.fixed_point` in Mathlib. -/
theorem recursion_theorem {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  Nat.Partrec.Code.fixed_point hf

/-- Second recursion theorem (parametrised form): for any partial computable
`f : Code → ℕ →. ℕ` there is a code `c` whose semantics is `f c`.
This is `Nat.Partrec.Code.fixed_point₂` in Mathlib. -/
theorem recursion_theorem₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c :=
  Nat.Partrec.Code.fixed_point₂ hf

end CS


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

