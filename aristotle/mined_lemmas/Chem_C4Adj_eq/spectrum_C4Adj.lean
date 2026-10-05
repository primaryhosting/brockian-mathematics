/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix

namespace Chem

/-- The adjacency matrix (Hückel matrix with `α = 0`, `β = 1`) of the cycle graph `C₄`. -/

lemma spectrum_C4Adj : spectrum ℂ C4Adj = {2, 0, -2} := by
  ext r
  rw [mem_spectrum_iff_det_eq_zero, resolvent_matrix, det_cycle_four]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have h' : r ^ 2 * ((r - 2) * (r + 2)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact Or.inr (Or.inl (by simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1))
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl (by linear_combination h2)
      · exact Or.inr (Or.inr (by linear_combination h2))
  · rintro (rfl | rfl | rfl) <;> ring

/-- **Hückel theory for cyclobutadiene `C₄`.**
The eigenvalues of the adjacency matrix of the cycle graph `C₄` are exactly
`2 cos (2πk/4)` for `k = 0, 1, 2, 3` (namely `2, 0, -2, 0`). -/
