/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Math

open Finset SimpleGraph

/-- Extract four elements in increasing order from a four-element finset. -/

theorem paley_indep_check : ∀ a b c d : Fin 17, a < b → b < c → c < d →
    ¬ (paleyAdj a b = false ∧ paleyAdj a c = false ∧ paleyAdj a d = false ∧ paleyAdj b c = false ∧
      paleyAdj b d = false ∧ paleyAdj c d = false) := by
  decide

