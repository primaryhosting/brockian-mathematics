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

lemma wagner_no_indep4 : ¬ ∃ S : Finset (Fin 8), wagnerᶜ.IsNClique 4 S := by decide

