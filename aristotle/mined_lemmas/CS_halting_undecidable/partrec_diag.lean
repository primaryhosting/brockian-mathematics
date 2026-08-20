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

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- The diagonal partial function built from a candidate halting decider `H`:
on input `n` it loops forever if `H` says that the `n`-th program halts on input `n`,
and returns `0` otherwise. -/

theorem partrec_diag {H : Code → ℕ → Bool} (hH : Computable₂ H) : Nat.Partrec (diag H) := by
  have hc : Computable fun p : ℕ × ℕ => !H (Denumerable.ofNat Code p.1) p.1 :=
    (Primrec.not.to_comp).comp
      (hH.comp ((Computable.ofNat Code).comp Computable.fst) Computable.fst)
  have : Partrec (fun n : ℕ => Nat.rfind fun _ => Part.some (!H (Denumerable.ofNat Code n) n)) :=
    Partrec.rfind (p := fun n _ : ℕ => (Part.some (!H (Denumerable.ofNat Code n) n) : Part Bool))
      (Computable₂.partrec₂ (f := fun n _ : ℕ => !H (Denumerable.ofNat Code n) n) hc)
  exact Partrec.nat_iff.mp this

/-- **The halting problem is undecidable.**

There is no total computable function `H` which, given (a code for) a program `c` and an
input `x`, decides whether `c` halts on `x`.  The proof is by diagonalization: from such an
`H` one builds a partial recursive function that halts on the index `n` of a program exactly
when `H` claims that program does *not* halt on `n`, and applies it to its own index. -/
