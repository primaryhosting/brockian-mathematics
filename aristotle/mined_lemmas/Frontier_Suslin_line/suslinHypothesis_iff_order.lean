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

set_option grind.warning false

/-!
## Suslin's problem

Cantor characterised the real line as (up to order isomorphism) the unique nonempty complete
dense linear order without endpoints which is *separable*.  Suslin asked whether "separable"
can be weakened to the *countable chain condition* (ccc): every family of pairwise disjoint
nonempty open sets is countable.  A counterexample — a ccc, non-separable dense linear order
without endpoints, equipped with its order topology — is called a **Suslin line**, and
**Suslin's Hypothesis** (`SuslinHypothesis`) is the assertion that no Suslin line exists.

Suslin's Hypothesis is independent of ZFC (Jech, Tennenbaum, Solovay–Tennenbaum): Jensen's
diamond principle `◊` implies that a Suslin line exists, while `MA + ¬CH` implies that none
does.  Neither implication can be settled inside ZFC alone, so neither `SuslinHypothesis`
nor its negation is provable here.  What this file does is:

* give a precise formalisation of the notions involved (`IsCellularFamily`, `IsCCC`,
  `IsSuslinLine`, `SuslinHypothesis`);
* prove that Suslin's Hypothesis is *equivalent* to the classical topological statement
  "every ccc dense linear order without endpoints is separable";
* prove a **Lean-checked reduction** of Suslin's problem to a purely order-theoretic
  (topology-free) statement: every dense linear order without endpoints all of whose
  families of pairwise disjoint nonempty open intervals are countable has a countable
  order-dense subset;
* prove the *base case*: separable spaces are ccc, so a Suslin line is exactly a
  counterexample to the converse; in particular `ℝ` is not a Suslin line, and no Suslin
  line is countable, second countable, or topologically embeddable in `ℝ`.
-/

namespace Frontier

open Set TopologicalSpace Topology

universe u

/-- A *cellular family* in a topological space: a family of pairwise disjoint nonempty
open sets. -/

theorem suslinHypothesis_iff_order :
    SuslinHypothesis.{u} ↔
      ∀ (X : Type u) [LinearOrder X],
        Nonempty X → DenselyOrdered X → NoMinOrder X → NoMaxOrder X → IntervalCCC X →
        HasCountableOrderDenseSubset X := by
  rw [suslinHypothesis_iff_topological]
  constructor
  · intro H X _ hne hd hmin hmax hI
    letI : TopologicalSpace X := Preorder.topology X
    haveI : OrderTopology X := ⟨rfl⟩
    haveI := hd
    haveI : Nontrivial X := by
      haveI := hmin
      obtain ⟨x⟩ := hne
      obtain ⟨y, hy⟩ := exists_lt x
      exact ⟨x, y, ne_of_gt hy⟩
    haveI := H X hne hd hmin hmax (isCCC_iff_intervalCCC.2 hI)
    exact separableSpace_iff_hasCountableOrderDenseSubset.1 inferInstance
  · intro H X _ _ _ hne hd hmin hmax hccc
    haveI := hd
    haveI : Nontrivial X := by
      haveI := hmin
      obtain ⟨x⟩ := hne
      obtain ⟨y, hy⟩ := exists_lt x
      exact ⟨x, y, ne_of_gt hy⟩
    exact separableSpace_iff_hasCountableOrderDenseSubset.2
      (H X hne hd hmin hmax (isCCC_iff_intervalCCC.1 hccc))

/-- **Suslin's problem.**

1. Suslin's Hypothesis is equivalent to the classical topological statement: every ccc dense
   linear order without endpoints is separable.
2. It is equivalent to a purely order-theoretic statement, with no topology involved.
3. Separability always implies the countable chain condition, so a Suslin line is precisely a
   counterexample to the converse implication for order topologies.
4. Base case: `ℝ` is not a Suslin line; and no Suslin line is countable, second countable, or
   topologically embeddable in `ℝ`.
-/
