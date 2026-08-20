/-
# Recursion Theorem
Category: Frontier Cs
Target: CS.recursion_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.Computability.PartrecCode

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
