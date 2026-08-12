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

namespace CS

open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Rice's theorem**: every nontrivial semantic (extensional) property of programs is
undecidable.

Here programs are the codes `Nat.Partrec.Code` for the partial recursive functions, and
`eval` sends a code to the partial function it computes.  A property `C : Set Code` is
*semantic* if it only depends on the computed function (`hsem`), and *nontrivial* if some
program has the property and some program does not (`hf`, `hg`).  Under these hypotheses
`C` is not decidable. -/
theorem rice_nontrivial (C : Set Code)
    (hsem : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C))
    (hf : ∃ cf : Code, cf ∈ C) (hg : ∃ cg : Code, cg ∉ C) :
    ¬ ComputablePred (fun c : Code => c ∈ C) := by
  intro h
  rcases (ComputablePred.rice₂ C hsem).1 h with rfl | rfl
  · obtain ⟨cf, hcf⟩ := hf
    exact hcf
  · obtain ⟨cg, hcg⟩ := hg
    exact hcg (Set.mem_univ cg)

end CS

