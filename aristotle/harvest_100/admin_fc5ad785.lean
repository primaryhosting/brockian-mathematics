import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
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

/-- **Rice's theorem** (nontrivial form): a set `C` of program codes which is *semantic*
(membership depends only on the partial function computed by the code) and *nontrivial*
(some program is in `C` and some program is not) is undecidable.

This is a direct consequence of `ComputablePred.rice₂` in Mathlib. -/
theorem rice_nontrivial (C : Set Code)
    (hsem : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C))
    (hin : ∃ cf : Code, cf ∈ C) (hout : ∃ cg : Code, cg ∉ C) :
    ¬ ComputablePred fun c : Code => c ∈ C := by
  intro h
  obtain ⟨cf, hcf⟩ := hin
  obtain ⟨cg, hcg⟩ := hout
  rcases (ComputablePred.rice₂ C hsem).1 h with rfl | rfl
  · exact hcf
  · exact hcg (Set.mem_univ cg)

end CS

