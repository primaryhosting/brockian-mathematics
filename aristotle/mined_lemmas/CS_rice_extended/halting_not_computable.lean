/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
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

set_option grind.warning false

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- `phi n` is the partial function computed by the program with index `n`
(the standard enumeration of partial recursive functions, obtained from the
Gödel numbering of `Nat.Partrec.Code`). -/

theorem halting_not_computable (m : ℕ) :
    ¬ ComputablePred (fun n : ℕ => (phi n m).Dom) := by
  intro h
  refine ComputablePred.halting_problem m ?_
  obtain ⟨_, h⟩ := h
  refine ⟨by infer_instance, ?_⟩
  simpa [phi, Denumerable.ofNat_encode] using h.comp (Computable.encode (α := Code))

/-- An instance of `rice_extended`: the set of indices of programs computing the
everywhere-undefined function is not recursive. -/
