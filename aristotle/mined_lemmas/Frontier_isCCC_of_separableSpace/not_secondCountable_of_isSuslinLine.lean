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

theorem not_secondCountable_of_isSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X]
    (h : IsSuslinLine X) : ¬ SecondCountableTopology X := fun _ => h.not_separable inferInstance

/-- A linear order with a countable *order-dense* subset (one meeting every nonempty open
interval) is separable in the order topology. -/
