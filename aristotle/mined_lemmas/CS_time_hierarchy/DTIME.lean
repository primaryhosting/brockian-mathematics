import Mathlib

/-!
# Time Hierarchy
Category: Frontier Cs
Target: CS.time_hierarchy
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

open Nat.Partrec Nat.Partrec.Code Denumerable Encodable

/-- A language: a decision problem whose instances are encoded as natural numbers. -/
abbrev Language : Type := ℕ → Bool

/-- `DTIME t` is the class of languages decided by some partial recursive program
(a `Nat.Partrec.Code`) within `t n` steps on input `n`, where "steps" is measured by the
step-indexed evaluator `Nat.Partrec.Code.evaln`: the machine must output `1` on inputs in the
language and `0` on inputs outside it, using at most `t n` fuel. -/

def DTIME (t : ℕ → ℕ) : Set Language :=
  {L | ∃ c : Code, ∀ n : ℕ, evaln (t n) c n = some (if L n then 1 else 0)}

/-- Time classes are monotone in the time bound. -/
