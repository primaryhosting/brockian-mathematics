import Mathlib
/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finset of all boolean words (lists) of length `n`. -/

def ext (L : ℕ) (c : List Bool) : Finset (List Bool) :=
  (words (L - c.length)).image (fun w => c ++ w)

