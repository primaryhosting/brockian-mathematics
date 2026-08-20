/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A tuple of integers `H` is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuple conjecture) when, for every prime `p`, the residues of the entries
of `H` modulo `p` do not cover all of `ZMod p`. -/

theorem AdmissibilityKTupleK4 : IsAdmissibleTuple [0, 2, 6, 8] := by
  intro p hp
  rcases lt_or_ge p 5 with h5 | h5
  · have h2 := hp.two_le
    interval_cases p
    · exact ⟨1, by decide⟩
    · exact ⟨1, by decide⟩
    · exact absurd hp (by decide)
  · exact exists_residue_not_hit _ p hp (by simpa using h5)

end Brockian

