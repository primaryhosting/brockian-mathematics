/-
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 4 4
Category: Pure Mathematics
Target: Math.ramsey_4_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Finset SimpleGraph

/-! ### Generic clique helpers -/

section Helpers
variable {V : Type*} {G : SimpleGraph V}

/-- A set with no internal `G`-edges is a clique of the complement. -/

lemma paley_no_four : ∀ a b c d : Fin 17,
    ¬(paleyAdj a b ∧ paleyAdj a c ∧ paleyAdj a d ∧ paleyAdj b c ∧ paleyAdj b d ∧ paleyAdj c d) := by
  decide +kernel

