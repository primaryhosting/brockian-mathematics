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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Suslin's problem

Cantor characterised the real line as (up to order isomorphism) the unique
nonempty separable dense linear order without endpoints that is complete.
*Suslin's problem* asks whether "separable" may be weakened to the
**countable chain condition** (ccc): every family of pairwise disjoint nonempty
open sets is countable.  Separability implies ccc (`Frontier.isCcc_of_separable`
below), so the question is whether the two conditions coincide for dense linear
orders.

A **Suslin line** is a counterexample: a nontrivial dense linear order without
endpoints, carrying the order topology, which is ccc but *not* separable.
**Suslin's Hypothesis** (`Frontier.SuslinHypothesis`) is the statement that no
Suslin line exists.

Suslin's Hypothesis is independent of ZFC: Jensen's diamond principle `◊`
(which holds in Gödel's constructible universe `L`) implies that a Suslin line
exists, while `MA_{ℵ₁} + ¬CH` implies that none does.  Consequently the
phrasing "a Suslin line exists iff ◊-type hypotheses fail" is *not* a theorem —
both `◊` and its failure are consistent with the existence of a Suslin line
being false, and the existence of a Suslin line is simply not decided by ZFC
(so, in particular, it is not provably equivalent to any ZFC-refutable or
ZFC-provable statement).  What can be established inside Lean/ZFC is the precise
formulation of the problem together with the ZFC-provable reductions; those are
what is proved here, in `Frontier.Suslin_line`:

* separability implies ccc, so a Suslin line, if any, is a genuine gap between
  the two conditions;
* the real line is not a Suslin line;
* a Suslin line is uncountable, is not second countable, and is not order
  isomorphic to `ℝ`;
* Suslin's Hypothesis is equivalent to the assertion that every ccc dense
  linear order without endpoints (with the order topology) is separable.
-/

namespace Frontier

open TopologicalSpace

/-- The **countable chain condition**: every family of pairwise disjoint
nonempty open sets is countable. -/

theorem isEmpty_orderIso_real_of_isSuslinLine (α : Type*) [LinearOrder α] [TopologicalSpace α]
    (h : IsSuslinLine α) : IsEmpty (α ≃o ℝ) :=
  ⟨fun e => (isEmpty_orderEmbedding_real_of_isSuslinLine α h).elim e.toOrderEmbedding⟩

/-- **Cantor's base case.** A countable nontrivial dense linear order without endpoints is
order isomorphic to `ℚ`; in particular (being countable) it is separable and hence not a
Suslin line. -/
