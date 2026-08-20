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

def SuslinHypothesis : Prop :=
  ∀ (X : Type) (i : LinearOrder X) (τ : TopologicalSpace X), ¬ @IsSuslinLine X i τ

/-- Every separable space satisfies the countable chain condition.  This is the reason a Suslin
line is a genuine weakening of the classical characterisation of `ℝ`: it is the Mathlib lemma
`Set.PairwiseDisjoint.countable_of_isOpen`. -/
