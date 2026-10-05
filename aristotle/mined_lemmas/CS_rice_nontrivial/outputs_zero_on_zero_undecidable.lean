/-
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Rice's theorem.**  Let `C` be any set of partial functions `ℕ →. ℕ`, i.e. a *semantic*
property of programs (it depends only on the partial function a program computes).  If `C` is
nontrivial, in the sense that some program's semantics lies in `C` and some other program's
semantics does not, then the property "the program `c` has semantics in `C`" is undecidable. -/

theorem outputs_zero_on_zero_undecidable :
    ¬ ComputablePred (fun c : Code => c.eval 0 = Part.some 0) := by
  refine rice_nontrivial_pred _ (fun c d h => by rw [h]) ⟨Code.zero, rfl⟩ ⟨Code.succ, ?_⟩
  have h1 : (Code.succ).eval 0 = Part.some 1 := by simp [Nat.Partrec.Code.eval]
  simp [h1]

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

