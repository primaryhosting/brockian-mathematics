/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Math

open Finset

/-- `RamseyProp n s t` says: every simple graph on `n` vertices contains either a clique of
size `s` or an independent set (a clique in the complement) of size `t`. -/

lemma card_triple [DecidableEq V] (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
    Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]

end Basic

/-! ## Monotonicity in the number of vertices -/

section Mono

