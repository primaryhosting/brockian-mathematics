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
