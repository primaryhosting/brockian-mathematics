/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is joined to `i + 1` and to `i - 1`.  For `n ≥ 3` this is exactly the adjacency matrix
of the simple cycle graph `C n`; for `n = 1, 2` it is the circulant matrix `S + S⁻¹` (`S` the
cyclic shift), which is the convention under which the Hückel spectrum formula holds. -/

lemma cycleAdj_mulVec (n : ℕ) [NeZero n] (v : ZMod n → ℂ) (i : ZMod n) :
    (cycleAdj n).mulVec v i = v (i + 1) + v (i - 1) := by
  simp [cycleAdj, Matrix.mulVec, dotProduct, add_mul, Finset.sum_add_distrib]

/-- A primitive `n`-th root of unity. -/
