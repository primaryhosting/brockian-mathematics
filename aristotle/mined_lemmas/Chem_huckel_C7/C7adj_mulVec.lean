/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem C7adj_mulVec (v : ZMod 7 → ℂ) (i : ZMod 7) :
    C7adj.mulVec v i = v (i - 1) + v (i + 1) := by
  simp only [Matrix.mulVec, dotProduct, C7adj_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq' Finset.univ]
  simp

/-! ### The primitive 7-th root of unity -/

/-- The primitive `7`-th root of unity `exp(2πi/7)`. -/
