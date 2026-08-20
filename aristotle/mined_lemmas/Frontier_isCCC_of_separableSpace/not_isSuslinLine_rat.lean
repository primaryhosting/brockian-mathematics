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

theorem not_isSuslinLine_rat : ¬ IsSuslinLine ℚ :=
  not_isSuslinLine_of_separableSpace ℚ

/-- **Suslin's problem, precisely stated, together with the elementary reductions.**

1. A Suslin line exists if and only if Suslin's Hypothesis fails (this fixes the precise meaning
   of the problem; the two sides are the two horns of the ZFC-independent dichotomy, `◊` giving
   a Suslin line and `MA + ¬CH` giving SH).
2. Every separable space is ccc, so the ccc requirement in the definition of a Suslin line is a
   genuine weakening of separability (Mathlib: `Set.PairwiseDisjoint.countable_of_isOpen`).
3. No separable linear order is a Suslin line; in particular a Suslin line must be uncountable,
   fail to be second countable, and have no countable order-dense subset.
4. Base cases: neither `ℝ` nor `ℚ` is a Suslin line. -/
