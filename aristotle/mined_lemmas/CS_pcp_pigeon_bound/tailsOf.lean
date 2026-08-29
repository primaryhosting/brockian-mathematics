/-
# Pcp Pigeon Bound
Category: Computer Science
Target: CS.pcp_pigeon_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kraft's inequality for prefix-free binary codes

A finite set `S` of binary codewords (lists of booleans) is *prefix-free* if no codeword
is a prefix of a different codeword.  The main result, `CS.pcp_pigeon_bound`, states
Kraft's inequality: `∑ w ∈ S, (1/2) ^ w.length ≤ 1`.
-/

namespace CS

/-- A finite set of binary codewords is *prefix-free* when no codeword is a prefix of
another codeword. -/

def tailsOf (b : Bool) (S : Finset (List Bool)) : Finset (List Bool) :=
  (S.filter (fun w => w.headI = b)).image List.tail

