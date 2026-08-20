/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₃`: every pair of distinct vertices
is joined by an edge, and there are no loops. -/

lemma two_cos_two_pi_k_div_three (k : Fin 3) :
    2 * Real.cos (2 * Real.pi * (k : ℝ) / 3) = 2 ∨
      2 * Real.cos (2 * Real.pi * (k : ℝ) / 3) = -1 := by
  obtain ⟨k, hk⟩ := k
  interval_cases k
  · left; norm_num
  · right; simpa using two_cos_two_pi_div_three
  · right; simpa using two_cos_four_pi_div_three

/-- **Hückel theory for the cyclic C₃ system.**
The eigenvalues of the adjacency matrix of the cycle graph `C₃` are exactly the
numbers `2 cos (2πk/3)` for `k = 0, 1, 2`. -/
