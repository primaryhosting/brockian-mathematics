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

open Nat.Partrec Nat.Partrec.Code

/-- The partial function computed by the program with (Gödel) index `n`. -/

theorem partrec_phi (n : ℕ) : Nat.Partrec (phi n) :=
  Nat.Partrec.Code.exists_code.2 ⟨Denumerable.ofNat Nat.Partrec.Code n, rfl⟩

/--
**Kleene's recursion (fixed point) theorem.**
Every computable transformation `f` of program indices has a fixed point *up to
extensional behaviour*: there is an index `n` whose program computes exactly the
same partial function as the transformed program `f n`.
-/
