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

open Nat.Partrec Nat.Partrec.Code

/-- A property `C` of programs (codes) is *semantic* (extensional) if it depends only on the
partial function the program computes: two programs with the same denotation are
indistinguishable by `C`. -/
def Semantic (C : Set Nat.Partrec.Code) : Prop :=
  ∀ c₁ c₂ : Nat.Partrec.Code, Nat.Partrec.Code.eval c₁ = Nat.Partrec.Code.eval c₂ →
    (c₁ ∈ C ↔ c₂ ∈ C)

/-- A property `C` of programs is *nontrivial* if some program has it and some program
does not. -/
def NontrivialProperty (C : Set Nat.Partrec.Code) : Prop :=
  (∃ c : Nat.Partrec.Code, c ∈ C) ∧ ∃ c : Nat.Partrec.Code, c ∉ C

/-- **Rice's theorem**: every nontrivial semantic property of programs is undecidable. -/
theorem rice_nontrivial (C : Set Nat.Partrec.Code) (hsem : Semantic C)
    (hnt : NontrivialProperty C) : ¬ ComputablePred (fun c : Nat.Partrec.Code => c ∈ C) := by
  intro hcomp
  obtain ⟨⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩⟩ := hnt
  rcases (ComputablePred.rice₂ C hsem).1 hcomp with hemp | huniv
  · exact absurd (hemp ▸ hc₀) (Set.notMem_empty c₀)
  · exact hc₁ (huniv ▸ Set.mem_univ c₁)

end CS

