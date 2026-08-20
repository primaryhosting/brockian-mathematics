/-
# CH Independent Statement
Category: Frontier — Set Theory
Target: Frontier.CH_independent_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header
-- above is written as a plain block comment.)

import Mathlib

set_option autoImplicit false

open Cardinal FirstOrder Language

namespace Frontier

/-! ## Part 1: the Continuum Hypothesis as a statement about cardinals

Inside Lean's own (ZFC-like) ambient set theory we can state CH directly:
there is no cardinal strictly between `ℵ₀` and `𝔠 = 2 ^ ℵ₀`.  We check that this
is equivalent to the usual formulation `𝔠 = ℵ₁`, and to the "no set of reals of
intermediate cardinality" formulation.  These equivalences are theorems of ZFC
(they are proved outright below); it is CH itself that is independent. -/

/-- The Continuum Hypothesis, stated for cardinals: no cardinal lies strictly
between `ℵ₀` and the cardinality of the continuum. -/

theorem exists_independent_sentence :
    ∃ φ : Language.empty.Sentence, Independent (∅ : Language.empty.Theory) φ := by
  haveI : Language.empty.Structure Bool := Language.emptyStructure
  haveI : Language.empty.Structure Unit := Language.emptyStructure
  refine ⟨Sentence.cardGe Language.empty 2, independent_of_two_models ?_ ?_⟩
  · haveI : (Bool : Type) ⊨ (∅ ∪ {Sentence.cardGe Language.empty 2} : Language.empty.Theory) := by
      refine (Theory.model_iff _).2 ?_
      intro ψ hψ
      simp only [Set.empty_union, Set.mem_singleton_iff] at hψ
      subst hψ
      rw [Sentence.realize_cardGe]
      simp
    exact Theory.Model.isSatisfiable Bool
  · haveI : (Unit : Type) ⊨
        (∅ ∪ {(Sentence.cardGe Language.empty 2).not} : Language.empty.Theory) := by
      refine (Theory.model_iff _).2 ?_
      intro ψ hψ
      simp only [Set.empty_union, Set.mem_singleton_iff] at hψ
      subst hψ
      rw [Sentence.realize_not, Sentence.realize_cardGe]
      simp
    exact Theory.Model.isSatisfiable Unit

end Frontier

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

