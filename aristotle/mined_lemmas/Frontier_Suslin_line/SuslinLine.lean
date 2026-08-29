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

theorem SuslinLine.isEmpty_orderIso_real (L : SuslinLine) : IsEmpty (L.carrier ≃o ℝ) := by
  constructor
  intro e
  refine L.isSuslinLine.2.2.2.2 ?_
  have hcont : Continuous (e.symm : ℝ → L.carrier) := (e.symm).continuous
  have hdr : DenseRange (e.symm : ℝ → L.carrier) :=
    Function.Surjective.denseRange (e.symm).surjective
  exact hdr.separableSpace hcont

/-!
## The target statement

We record: (i) the general fact that separability implies the countable chain condition, so
that a Suslin line is exactly a space witnessing the failure of the converse in the class of
dense unbounded linear orders; (ii) the base case that `ℝ` is not a Suslin line; (iii) the
precise formulation of Suslin's problem as the equivalence between the existence of a Suslin
line and the failure of Suslin's Hypothesis; and (iv) structural consequences: any Suslin line
is uncountable, is not second countable, and is not order isomorphic to `ℝ`.
-/

/-- **Suslin's problem.**

* every separable space is ccc (so a Suslin line is precisely a dense unbounded linear order
  witnessing that the converse fails);
* `ℝ` is ccc, separable, and hence not a Suslin line (base case);
* a Suslin line exists if and only if Suslin's Hypothesis fails;
* every Suslin line is uncountable, is not second countable, and is not order isomorphic
  to `ℝ`;
* in every Suslin line each pairwise disjoint family of nonempty open intervals is countable,
  while no countable subset is dense (the ccc-versus-separability tension in explicit form).

The existence of a Suslin line is independent of ZFC, so no ZFC proof can decide the middle
equivalence; what is proved here is the precise reduction together with the ZFC-provable facts
surrounding it. -/
