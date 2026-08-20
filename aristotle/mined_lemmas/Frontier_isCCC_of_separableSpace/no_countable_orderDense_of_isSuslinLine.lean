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

theorem no_countable_orderDense_of_isSuslinLine (X : Type u) [LinearOrder X]
    [TopologicalSpace X] (hX : IsSuslinLine X) :
    ¬ ∃ D : Set X, D.Countable ∧ ∀ a b : X, a < b → ∃ c ∈ D, a < c ∧ c < b := by
  rintro ⟨D, hD, hdense⟩
  haveI := hX.orderTopology
  haveI : Nontrivial X := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact not_countable_of_isSuslinLine X hX inferInstance
  exact hX.not_separable (separableSpace_of_countable_orderDense X hD hdense)

/-- The real line is not a Suslin line: it is separable (`ℚ` is dense in it). -/
