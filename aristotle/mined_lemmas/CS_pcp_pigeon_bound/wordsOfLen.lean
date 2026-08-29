import Mathlib

/-!
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- The finset of all binary words of a given length. -/

def wordsOfLen : ℕ → Finset (List Bool)
  | 0 => {[]}
  | (n + 1) => Finset.univ.biUnion (fun b : Bool => (wordsOfLen n).image (b :: ·))

