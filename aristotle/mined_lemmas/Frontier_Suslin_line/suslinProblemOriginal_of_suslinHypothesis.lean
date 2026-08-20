import Mathlib
import RequestProject.CantorDedekind

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open TopologicalSpace Set

namespace Frontier

/-- The **countable chain condition** (ccc) for a topological space `X`: every family of
pairwise disjoint nonempty open subsets of `X` is countable. -/

theorem suslinProblemOriginal_of_suslinHypothesis (h : SuslinHypothesis) :
    SuslinProblemOriginal :=
  suslinProblemOriginal_iff.mpr fun X _ _ _ => h X inferInstance inferInstance

/-- **Suslin line.**

The package: (1) separability implies ccc for any topological space, so the ccc half of the
definition of a Suslin line is the weakening of separability that Suslin's problem is about;
(2) `ℝ` is not a Suslin line; (3) any Suslin line is uncountable; (4) no Suslin line is
homeomorphic to `ℝ`; (5) Suslin's Hypothesis is equivalent to the assertion that every ccc
dense endpointless linearly ordered topological space is separable; (6) Suslin's original
problem (is every ccc complete dense endpointless linear order order-isomorphic to `ℝ`?) has
a positive answer exactly when there is no complete Suslin line; and (7) Suslin's Hypothesis
implies a positive answer to Suslin's original problem. -/
