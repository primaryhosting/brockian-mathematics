import Mathlib

/-!
# Rice Nontrivial
Category: Computer Science
Target: CS.rice_nontrivial
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

open scoped Classical

/-- A property `C` of programs (codes) is *semantic* (extensional) if it depends only on the
partial function the program computes. -/
def Semantic (C : Set Code) : Prop :=
  ∀ c₁ c₂ : Code, eval c₁ = eval c₂ → (c₁ ∈ C ↔ c₂ ∈ C)

/-- A property `C` of programs is *nontrivial* if some program has it and some program lacks it. -/
def Nontrivial (C : Set Code) : Prop :=
  (∃ c, c ∈ C) ∧ ∃ c, c ∉ C

/-- If membership in a set of codes is decidable by a computable procedure, then the "flip"
function, sending codes in `C` to a fixed code `a` and codes outside `C` to a fixed code `b`,
is computable. -/
theorem computable_flip {C : Set Code} (h : ComputablePred fun c => c ∈ C) (a b : Code) :
    Computable fun c => if c ∈ C then a else b := by
  obtain ⟨_, hc⟩ := h
  refine (Computable.cond hc (Computable.const a) (Computable.const b)).of_eq fun c => ?_
  by_cases hcC : c ∈ C <;> simp [hcC]

/-- **Rice's theorem.** Every nontrivial semantic property of programs is undecidable. -/
theorem rice_nontrivial (C : Set Code) (hsem : Semantic C) (hnt : Nontrivial C) :
    ¬ ComputablePred fun c => c ∈ C := by
  intro h
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hnt
  -- The flip function maps programs in `C` to `b ∉ C`, and programs outside `C` to `a ∈ C`.
  obtain ⟨c, hc⟩ := fixed_point (computable_flip h b a)
  -- By Kleene's recursion theorem the flip has a semantic fixed point, which is absurd.
  have hiff : (if c ∈ C then b else a) ∈ C ↔ c ∈ C := hsem _ _ hc
  by_cases hcC : c ∈ C
  · rw [if_pos hcC] at hiff
    exact hb (hiff.2 hcC)
  · rw [if_neg hcC] at hiff
    exact hcC (hiff.1 ha)

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

