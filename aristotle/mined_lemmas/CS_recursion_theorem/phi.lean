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

Programs are the partial recursive codes `Nat.Partrec.Code`, indexed by natural numbers via
the `Denumerable` enumeration; `CS.phi n` is the partial function computed by the `n`-th
program. The main result `CS.recursion_theorem` states that for every total computable
`f : ℕ → ℕ` on program indices there is an index `n` with `phi (f n) = phi n`.

The proof is the usual diagonal argument via the s-m-n theorem (`Nat.Partrec.Code.curry`)
and the universal machine (`Nat.Partrec.Code.eval_part`).
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

set_option grind.warning false

namespace CS

open Nat.Partrec Nat.Partrec.Code Computable Partrec

/-- The partial function computed by the `n`-th program in the standard enumeration of
partial recursive codes. -/

noncomputable def phi (n : ℕ) : ℕ →. ℕ := eval (Denumerable.ofNat Code n)

/-- The "self-application" helper used in the diagonal argument: `diagEval x y` runs the
program with index `x` on input `x`, and then runs the program whose index is the result
on input `y`. -/
