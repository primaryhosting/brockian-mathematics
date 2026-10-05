import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Frontier

/-!
## Suslin's problem, stated precisely

Cantor characterised the real line: up to order isomorphism, `ℝ` is the unique
*separable* linear continuum (a nonempty, densely ordered, Dedekind complete
linear order without endpoints whose order topology has a countable dense set).

Suslin asked whether "separable" can be weakened to the *countable chain
condition* (ccc): every family of pairwise disjoint nonempty open sets is
countable.  A **Suslin line** is a counterexample: a ccc linear continuum that
is not separable.  *Suslin's Hypothesis* (`SuslinHypothesis` below) is the
statement that no Suslin line exists.

Suslin's Hypothesis is independent of ZFC: Jensen showed that Gödel's diamond
principle `◇` (which holds in `L`) yields a Suslin line, while Solovay and
Tennenbaum showed that `MA + ¬CH` implies that none exists.  Hence neither
`SuslinHypothesis` nor its negation is provable, and this file does not attempt
to prove either.  What is proved here is the ZFC-provable content surrounding
the problem:

* `separableSpace_hasCCC`: separability always implies ccc, in any topological
  space.  This is what makes Suslin's question a genuine weakening of Cantor's
  hypothesis, and it shows that the two defining features of a Suslin line
  (ccc, non-separable) point in a consistent direction.
* `IsSuslinLine.uncountable`: a Suslin line is necessarily uncountable.
* `not_isSuslinLine_real`: the real line is not a Suslin line.
* `suslinHypothesis_iff`: the precise reduction of Suslin's Hypothesis to the
  statement "every ccc linear continuum is separable".
-/

/-- The **countable chain condition**: every family of pairwise disjoint
nonempty open sets is countable. -/
def HasCCC (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (ι : Type u) (U : ι → Set X), (∀ i, IsOpen (U i)) → (∀ i, (U i).Nonempty) →
    (Pairwise fun i j => Disjoint (U i) (U j)) → Countable ι

/-- A **linear continuum**: a nontrivial, densely ordered, Dedekind complete
linear order without endpoints.  (Up to order isomorphism, `ℝ` is the unique
*separable* such order — Cantor's theorem.) -/
def IsLinearContinuum (X : Type u) [LinearOrder X] : Prop :=
  Nontrivial X ∧ DenselyOrdered X ∧ NoMinOrder X ∧ NoMaxOrder X ∧
    ∀ s : Set X, s.Nonempty → BddAbove s → ∃ x, IsLUB s x

/-- A **Suslin line**: a linear continuum, equipped with its order topology,
which satisfies the countable chain condition but is not separable. -/
def IsSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X] : Prop :=
  IsLinearContinuum X ∧ HasCCC X ∧ ¬ TopologicalSpace.SeparableSpace X

/-- **Suslin's Hypothesis**: there is no Suslin line, i.e. every ccc linear
continuum (with its order topology) is separable. -/
def SuslinHypothesis : Prop :=
  ∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X], ¬ IsSuslinLine X

/-- Every separable topological space satisfies the countable chain condition. -/
theorem separableSpace_hasCCC (X : Type u) [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] : HasCCC X := by
  intro ι U hopen hne hdisj
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense X
  have := hDc.to_subtype
  -- pick a point of `D` inside each `U i`
  have hpick : ∀ i, ∃ d : D, (d : X) ∈ U i := by
    intro i
    obtain ⟨x, hxU, hxD⟩ := hDd.inter_open_nonempty (U i) (hopen i) (hne i)
    exact ⟨⟨x, hxD⟩, hxU⟩
  choose f hf using hpick
  refine Function.Injective.countable (f := f) ?_
  intro i j hij
  by_contra hne'
  have hd := hdisj hne'
  have h1 : (f i : X) ∈ U i := hf i
  have h2 : (f i : X) ∈ U j := by rw [hij]; exact hf j
  exact (Set.disjoint_left.mp hd h1) h2

/-- A Suslin line is uncountable: a countable space is separable. -/
theorem IsSuslinLine.uncountable (X : Type) [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] (h : IsSuslinLine X) : Uncountable X := by
  rw [← not_countable_iff]
  intro hc
  exact h.2.2 (by infer_instance)

/-- The real line is not a Suslin line: it is separable. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ := by
  intro h
  exact h.2.2 (by infer_instance)

/-- Suslin's Hypothesis is exactly the statement that every ccc linear
continuum is separable. -/
theorem suslinHypothesis_iff :
    SuslinHypothesis ↔
      ∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
        IsLinearContinuum X → HasCCC X → TopologicalSpace.SeparableSpace X := by
  constructor
  · intro h X _ _ _ hcont hccc
    by_contra hsep
    exact h X ⟨hcont, hccc, hsep⟩
  · intro h X _ _ _ hS
    exact hS.2.2 (h X hS.1 hS.2.1)

/-- **Suslin's problem, formalized.**

The four conjuncts are:

1. separability implies the countable chain condition in every topological
   space (so a Suslin line really is a weakening of Cantor's characterisation
   of `ℝ`, and its two defining properties are not accidentally compatible);
2. every Suslin line is uncountable;
3. the real line is not a Suslin line;
4. Suslin's Hypothesis — "no Suslin line exists" — is equivalent to
   "every ccc linear continuum is separable".

Whether a Suslin line exists is independent of ZFC (Jensen: `◇` produces one;
Solovay–Tennenbaum: `MA + ¬CH` refutes them all), so no ZFC proof of either
`SuslinHypothesis` or its negation is possible; the content above is the
ZFC-provable part of the problem. -/
theorem Suslin_line :
    (∀ (X : Type) [TopologicalSpace X], TopologicalSpace.SeparableSpace X → HasCCC X) ∧
    (∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
        IsSuslinLine X → Uncountable X) ∧
    ¬ IsSuslinLine ℝ ∧
    (SuslinHypothesis ↔
      ∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
        IsLinearContinuum X → HasCCC X → TopologicalSpace.SeparableSpace X) := by
  refine ⟨fun X _ hsep => separableSpace_hasCCC X, fun X _ _ _ h => h.uncountable X,
    not_isSuslinLine_real, suslinHypothesis_iff⟩

end Frontier

