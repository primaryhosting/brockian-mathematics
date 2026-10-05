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
