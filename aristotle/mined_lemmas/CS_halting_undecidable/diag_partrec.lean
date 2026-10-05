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

/-
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Halting Undecidable
Category: Computer Science
Target: CS.halting_undecidable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Code Denumerable Encodable

/-- The diagonal partial function associated to a candidate halting decider `H`:
on input `n` it diverges exactly when `H` claims that the `n`-th program halts on
input `n`, and returns `0` otherwise. -/

theorem diag_partrec {H : Code → ℕ → Bool} (hH : Computable₂ H) :
    Nat.Partrec (diag H) := by
  have hb : Computable fun n : ℕ => H (ofNat Code n) n := hH.comp
    (Computable.ofNat _) Computable.id
  have : Partrec (diag H) :=
    Partrec.cond hb Partrec.none (Computable.const (0 : ℕ)).partrec
  simpa [Partrec] using this

/-- The diagonal function halts on `n` exactly when `H` says the `n`-th program
does not halt on `n`. -/
