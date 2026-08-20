/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Polynomial

/-- The cyclic shift matrix on `ZMod n`: it sends the standard basis vector `e i` to
`e (i - 1)`, equivalently `(shift n).mulVec v i = v (i + 1)`. -/

lemma shift_mulVec (n : ℕ) [NeZero n] (v : ZMod n → ℂ) (i : ZMod n) :
    (shift n).mulVec v i = v (i + 1) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (i + 1)]
  · simp [shift]
  · intro b _ hb; simp [shift, hb]
  · simp

/-- Every `n`-th root of unity is an eigenvalue of the cyclic shift, with the geometric
eigenvector `j ↦ μ ^ j`. -/
