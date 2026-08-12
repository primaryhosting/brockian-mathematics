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
theorem recursion_theorem {f : ℕ → ℕ} (hf : Computable f) :
    ∃ n : ℕ, eval (Denumerable.ofNat Code (f n)) = eval (Denumerable.ofNat Code n) := by
  -- Transport `f` to a computable transformation of codes.
  have hF : Computable fun c : Code => Denumerable.ofNat Code (f (Encodable.encode c)) :=
    Computable.ofNat Code |>.comp (hf.comp Computable.encode)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.fixed_point hF
  refine ⟨Encodable.encode c, ?_⟩
  simpa using hc

/-- **Kleene's recursion theorem** (code form): every computable transformation of codes `f`
has a fixed point up to the computed function: some code `c` computes the same partial function
as `f c`. -/
theorem recursion_theorem_code {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  Nat.Partrec.Code.fixed_point hf

/-- **Kleene's second recursion theorem**: for any partial computable `f : Code → ℕ →. ℕ`
there is a code `c` whose computed function is `f c`, i.e. a program that has access to
its own source code. -/
theorem recursion_theorem_self_reference {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c :=
  Nat.Partrec.Code.fixed_point₂ hf

end CS

#print axioms CS.recursion_theorem

