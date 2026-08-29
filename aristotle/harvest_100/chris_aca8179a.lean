import Mathlib.Computability.Halting

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- **Rice's theorem (nontrivial form).**
If a set `C` of programs (codes for partial recursive functions) is *semantic* — membership
depends only on the partial function `eval c` computed by the code `c` — and *nontrivial* —
some program lies in `C` and some program lies outside `C` — then `C` is undecidable.

This follows from Mathlib's `ComputablePred.rice₂`, which characterizes the decidable
semantic sets of codes as exactly `∅` and `Set.univ`. -/
theorem rice_nontrivial (C : Set Code)
    (hsem : ∀ cf cg : Code, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C))
    (hin : ∃ c : Code, c ∈ C) (hout : ∃ c : Code, c ∉ C) :
    ¬ ComputablePred fun c => c ∈ C := by
  intro h
  obtain ⟨c₀, hc₀⟩ := hin
  obtain ⟨c₁, hc₁⟩ := hout
  rcases (ComputablePred.rice₂ C hsem).1 h with rfl | rfl
  · exact hc₀
  · exact hc₁ (Set.mem_univ _)

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

