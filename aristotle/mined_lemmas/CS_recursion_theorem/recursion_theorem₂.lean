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

Kleene's recursion theorem: every computable transformation of programs has a fixed point.

Programs are modelled by `Nat.Partrec.Code`, the standard Mathlib type of codes for partial
recursive functions, whose semantics is `Nat.Partrec.Code.eval : Code → ℕ →. ℕ`.

The main theorem `CS.recursion_theorem` is given a self-contained proof from the universality
of `eval` (`Nat.Partrec.Code.eval_part`), the fact that partial recursive functions have codes
(`Nat.Partrec.Code.exists_code`), and the s-m-n theorem in the form
`Nat.Partrec.Code.primrec₂_curry` / `Nat.Partrec.Code.eval_curry`.
Mathlib also states this result directly as `Nat.Partrec.Code.fixed_point`
(and `Nat.Partrec.Code.fixed_point₂`); see `CS.recursion_theorem_via_mathlib` below.
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

/-- **Kleene's recursion theorem** (Rogers' fixed-point form): every computable
transformation `f` of programs has a fixed point up to semantics, i.e. there is a code `c`
such that the program `f c` computes exactly the same partial function as `c`.

Proof (Kleene's diagonal argument): let `g x y` run the program coded by `x` on input `x`,
read the result as a code, and run that code on `y`; `g` is partial recursive, say with code
`cg`. By the s-m-n theorem `n ↦ f (curry cg n)` is computable, so it has a code `cF`, and
`c := curry cg (encode cF)` is a fixed point: on input `n`, `c` first computes
`encode (f (curry cg (encode cF))) = encode (f c)` and then runs it on `n`. -/

theorem recursion_theorem₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) :
    ∃ c : Code, eval c = f c := by
  obtain ⟨cf, ef⟩ := exists_code.1 hf
  obtain ⟨c, hc⟩ :=
    recursion_theorem (f := fun c : Code => curry cf (encode c))
      (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp
  exact ⟨c, funext fun n => by simp [hc.symm, ef, eval_curry, Part.map_id']⟩

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

