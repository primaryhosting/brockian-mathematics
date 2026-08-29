import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
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

open Nat.Partrec Nat.Partrec.Code Encodable Denumerable

/-- The diagonal partial function associated with a candidate halting decider `H`:
on input `n`, it diverges when `H` claims that the `n`-th program halts on input `n`,
and returns `0` otherwise. -/

theorem partrec_diagFun {H : Nat.Partrec.Code → ℕ → Bool} (hH : Computable₂ H) :
    Nat.Partrec (diagFun H) := by
  have hdiag : Computable fun n : ℕ => H (ofNat Nat.Partrec.Code n) n :=
    hH.comp (Computable.ofNat Nat.Partrec.Code) Computable.id
  have : Partrec (diagFun H) :=
    Partrec.cond hdiag Partrec.none (Computable.const (0 : ℕ)).partrec
  exact Partrec.nat_iff.mp this

/-- **The halting problem is undecidable.**

There is no total computable function `H` which, given a program `p` (an element of the
type `Nat.Partrec.Code` of codes for partial recursive functions) and an input `x`,
correctly decides whether `p` halts on `x`.

The proof is by diagonalization: from such an `H` one builds the partial recursive function
which, on input `n`, diverges exactly when `H` says the `n`-th program halts on `n`.
Taking a code `e` for this function and running it on its own index yields a contradiction. -/
