import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace CS

/-- The finite set of all binary strings (lists of booleans) of length `n`. -/

def cube : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 => (cube n).image (List.cons false) ∪ (cube n).image (List.cons true)

