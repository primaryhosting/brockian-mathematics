/-
# Rice Extended
Category: Frontier Cs
Target: CS.rice_extended
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- A set of codes is *semantic* (extensional) if membership only depends on the
partial function computed by the code. -/

theorem rice_extended_partFun (C : Set (ℕ →. ℕ))
    (hin : ∃ cf : Code, eval cf ∈ C) (hout : ∃ cg : Code, eval cg ∉ C) :
    ¬ ComputablePred (fun c : Code => eval c ∈ C) := by
  intro h
  obtain ⟨cf, hcf⟩ := hin
  obtain ⟨cg, hcg⟩ := hout
  exact hcg
    (ComputablePred.rice C h
      (Partrec.nat_iff.1 <| eval_part.comp (Computable.const cf) Computable.id)
      (Partrec.nat_iff.1 <| eval_part.comp (Computable.const cg) Computable.id) hcf)

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

