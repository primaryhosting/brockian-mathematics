import Mathlib
/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Chem

/-- The Hückel (adjacency) matrix of the cycle `C₄`: `A i j = 1` exactly when the carbon
atoms `i` and `j` are neighbours in the four-membered ring. -/

lemma huckel_cos_three : 2 * Real.cos (2 * Real.pi * (3 : ℕ) / 4) = 0 := by
  rw [show (2 * Real.pi * (3 : ℕ) / 4 : ℝ) = Real.pi / 2 + Real.pi by push_cast; ring,
    Real.cos_add_pi, Real.cos_pi_div_two, neg_zero, mul_zero]

/-- The eigenvalues (spectrum) of the adjacency matrix of the cycle graph `C₄` are exactly the
Hückel values `2 cos (2πk/4)` for `k = 0, 1, 2, 3`, i.e. `2, 0, 0, -2`. -/
