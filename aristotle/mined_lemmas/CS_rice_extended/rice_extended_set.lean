/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Nat.Partrec Nat.Partrec.Code

namespace CS

/-- **Rice's theorem.** Let `P` be any property of partial functions `ℕ →. ℕ`
(a *semantic* property: it only sees the function computed, not the program).
If `P` is nontrivial, i.e. some program computes a function satisfying `P` and
some program computes a function not satisfying `P`, then the index set
`{c | P (eval c)}` is not recursive.

The proof is by Rogers' fixed point theorem
(`Nat.Partrec.Code.fixed_point`). -/

theorem rice_extended_set (P : (ℕ →. ℕ) → Prop)
    (h₁ : ∃ a : Code, P (eval a)) (h₂ : ∃ b : Code, ¬ P (eval b)) :
    ¬ ComputablePred (· ∈ {c : Code | P (eval c)}) :=
  rice_extended P h₁ h₂

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

