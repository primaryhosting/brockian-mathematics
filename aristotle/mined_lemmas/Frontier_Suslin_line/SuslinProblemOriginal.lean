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

def SuslinProblemOriginal : Prop :=
  ∀ (X : Type) (_ : ConditionallyCompleteLinearOrder X) (_ : TopologicalSpace X),
    OrderTopology X → DenselyOrdered X → NoMinOrder X → NoMaxOrder X → Nonempty X →
    CountableChainCondition X → Nonempty (X ≃o ℝ)

/-- Suslin's original problem has a positive answer exactly when there is no *complete*
Suslin line.  The nontrivial direction uses the Cantor–Dedekind theorem
`Frontier.orderIso_real_of_separableSpace`. -/
