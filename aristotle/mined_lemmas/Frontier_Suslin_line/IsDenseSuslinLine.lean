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
set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc): every family of pairwise disjoint nonempty open
sets is countable. -/

def IsDenseSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X] :
    Prop :=
  IsSuslinLine X ∧ DenselyOrdered X ∧ NoMinOrder X ∧ NoMaxOrder X

/-- **Suslin's Hypothesis** (SH): there is no Suslin line, i.e. every ccc linearly ordered
topological space is separable.  This statement is independent of ZFC:  Jensen showed that
Jensen's diamond principle `◊` (which holds in `L`) implies the existence of a Suslin line, hence
`¬ SH`, while Solovay and Tennenbaum showed that `MA + ¬CH` implies `SH`. -/
