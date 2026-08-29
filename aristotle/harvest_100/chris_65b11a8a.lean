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
def Semantic (C : Set Code) : Prop :=
  ∀ cf cg : Code, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)

/-- **Rice's theorem (extended form).**
The index set of a nontrivial semantic property is not recursive: if `C` is a set of
codes whose membership depends only on the computed partial function (`hsem`), and `C`
is nontrivial (some code is in `C` and some code is not), then `C` is not decidable. -/
theorem rice_extended (C : Set Code) (hsem : Semantic C)
    (hin : ∃ cf : Code, cf ∈ C) (hout : ∃ cg : Code, cg ∉ C) :
    ¬ ComputablePred (fun c : Code => c ∈ C) := by
  intro h
  obtain ⟨cf, hcf⟩ := hin
  obtain ⟨cg, hcg⟩ := hout
  rcases (ComputablePred.rice₂ C hsem).1 h with rfl | rfl
  · exact hcf
  · exact hcg (Set.mem_univ _)

/-- The same statement phrased for a property of partial functions: if `C` is a set of
partial functions containing the value of some code and omitting the value of some code,
then the set of codes computing a function in `C` is not decidable. -/
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

