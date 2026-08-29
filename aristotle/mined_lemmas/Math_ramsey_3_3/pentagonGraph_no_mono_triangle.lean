/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxRecDepth 10000

namespace Math


theorem pentagonGraph_no_mono_triangle :
    ∀ a b d : Fin 5, a ≠ b → a ≠ d → b ≠ d →
      ¬((pentagonGraph.Adj a b ∧ pentagonGraph.Adj a d ∧ pentagonGraph.Adj b d) ∨
        (¬ pentagonGraph.Adj a b ∧ ¬ pentagonGraph.Adj a d ∧ ¬ pentagonGraph.Adj b d)) := by
  decide

/-- **R(3,3) = 6**, graph-theoretic form: every simple graph on six vertices has
a triangle in itself or in its complement, and some simple graph on five
vertices (the 5-cycle) has neither. -/
