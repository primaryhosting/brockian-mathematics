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

theorem separableSpace_of_countable_orderDense (X : Type u) [LinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [Nontrivial X] {D : Set X} (hD : D.Countable)
    (h : ∀ a b : X, a < b → ∃ c ∈ D, a < c ∧ c < b) : SeparableSpace X :=
  ⟨⟨D, hD, dense_of_exists_between fun _ _ hab => h _ _ hab⟩⟩

/-- A Suslin line has no countable order-dense subset: there is no countable `D` meeting every
nonempty open interval. -/
