import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `ZMod 11`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/

lemma ch_add (a b : ZMod 11) : ch (a + b) = ch a * ch b := AddChar.map_add_eq_mul _ _ _

/-- `ch k + ch (-k) = 2 cos (2πk/11)`. -/
