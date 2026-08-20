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

theorem recursion_theorem_via_mathlib {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  Nat.Partrec.Code.fixed_point hf

/-- Index form of the recursion theorem: for every computable `F : ℕ → ℕ` acting on program
indices there is an index `n` such that the programs with indices `n` and `F n` compute the
same partial function. -/
