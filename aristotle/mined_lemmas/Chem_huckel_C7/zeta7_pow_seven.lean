import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertex `i` is adjacent to `i + 1` and to `i - 1`. -/

lemma zeta7_pow_seven : zeta7 ^ 7 = 1 := zeta7_isPrimitiveRoot.pow_eq_one

/-- Multiplication of a vector by the adjacency matrix of `C₇` is the discrete Laplacian-type
sum of the two neighbouring entries. -/
