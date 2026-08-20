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

lemma paley_no_four_non : ∀ a b c d : Fin 17,
    ¬(paleyNonAdj a b ∧ paleyNonAdj a c ∧ paleyNonAdj a d ∧ paleyNonAdj b c ∧ paleyNonAdj b d ∧
      paleyNonAdj c d) := by
  decide +kernel

