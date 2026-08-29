/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any module docstring, so the header block is repeated
-- below as the module docstring.)

import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open TopologicalSpace

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

namespace Frontier

/-!
## The countable chain condition

A *cellular family* in a topological space is a family of pairwise disjoint nonempty open
sets.  A space satisfies the *countable chain condition* (ccc) if every cellular family in it
is countable.
-/

/-- A family of pairwise disjoint nonempty open sets. -/

theorem suslinLine_nonempty_iff_not_suslinsHypothesis :
    Nonempty SuslinLine ↔ ¬ SuslinsHypothesis := by
  constructor
  · rintro ⟨L⟩ h
    obtain ⟨hd, hmin, hmax, hccc, hsep⟩ := L.isSuslinLine
    exact hsep (h L.carrier hd hmin hmax hccc)
  · intro h
    by_contra hne
    refine h ?_
    intro X _ _ _ hd hmin hmax hccc
    by_contra hsep
    exact hne ⟨⟨X, ⟨hd, hmin, hmax, hccc, hsep⟩⟩⟩

/-- The real line is not a Suslin line: it is a densely ordered, unbounded, ccc linear order,
but it *is* separable. -/
