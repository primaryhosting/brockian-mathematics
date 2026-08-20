/-
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Statement: Kleene's recursion theorem: every computable transformation of programs has a fixed point.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Statement: Kleene's recursion theorem: every computable transformation of programs has a fixed point.
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

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Kleene's recursion theorem** (index form).

Programs are identified with their Gödel numbers `n : ℕ`, and the (partial) function computed
by program `n` is `Nat.Partrec.Code.eval (Denumerable.ofNat Code n)`, i.e. the evaluation of the
code decoded from `n`.

For every *total computable* transformation of programs `f : ℕ → ℕ` there is a program `n`
(a fixed point) such that the program `f n` computes exactly the same partial function as `n`. -/

theorem recursion_theorem_self_reference {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c :=
  Nat.Partrec.Code.fixed_point₂ hf

end CS

#print axioms CS.recursion_theorem

