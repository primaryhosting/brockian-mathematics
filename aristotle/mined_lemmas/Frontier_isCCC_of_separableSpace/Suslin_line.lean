/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede any module docstring, so the header above is a
-- plain block comment and is repeated below as the module docstring.)

import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/

theorem Suslin_line :
    (SuslinLineExists ↔ ¬ SuslinHypothesis) ∧
    (∀ (X : Type u) (_ : TopologicalSpace X), SeparableSpace X → IsCCC X) ∧
    (∀ (X : Type u) (i : LinearOrder X) (τ : TopologicalSpace X),
        SeparableSpace X → ¬ @IsSuslinLine X i τ) ∧
    (∀ (X : Type u) (i : LinearOrder X) (τ : TopologicalSpace X), @IsSuslinLine X i τ →
        IsCCC X ∧ ¬ SeparableSpace X ∧ ¬ Countable X ∧ ¬ @SecondCountableTopology X τ ∧
        ¬ ∃ D : Set X, D.Countable ∧ ∀ a b : X, a < b → ∃ c ∈ D, a < c ∧ c < b) ∧
    (¬ IsSuslinLine ℝ ∧ ¬ IsSuslinLine ℚ) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, not_isSuslinLine_real, not_isSuslinLine_rat⟩
  · rintro ⟨X, i, τ, hX⟩ hSH
    exact hSH X i τ hX
  · intro hSH
    by_contra hne
    exact hSH fun X i τ hX => hne ⟨X, i, τ, hX⟩
  · intro X τ hsep
    exact @isCCC_of_separableSpace X τ hsep
  · intro X i τ hsep
    exact @not_isSuslinLine_of_separableSpace X i τ hsep
  · intro X i τ hX
    exact ⟨hX.ccc, hX.not_separable, not_countable_of_isSuslinLine X hX,
      not_secondCountable_of_isSuslinLine X hX, no_countable_orderDense_of_isSuslinLine X hX⟩

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

