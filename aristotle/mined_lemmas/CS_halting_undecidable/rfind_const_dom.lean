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

theorem rfind_const_dom (b : Bool) : (Nat.rfind fun _ => Part.some b).Dom ↔ b = true := by
  constructor
  · intro h
    have := Nat.rfind_spec (Part.get_mem h)
    simpa using this
  · intro h
    obtain ⟨n, hn, -⟩ := Nat.rfind_min' (p := fun _ => b) (m := 0) (by simp [h])
    exact Part.dom_iff_mem.2 ⟨n, hn⟩

