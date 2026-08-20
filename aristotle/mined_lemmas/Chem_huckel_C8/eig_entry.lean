/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C₈` (the Hückel π-system of cyclooctatetraene)
are `2 cos (2πk/8)` for `k = 0, …, 7`.  This is expressed as a complete factorisation of the
characteristic polynomial of the adjacency matrix of `SimpleGraph.cycleGraph 8`.

The proof diagonalises the adjacency matrix by the discrete Fourier matrix built from the
primitive eighth root of unity `ω = (√2/2)(1 + i)`.
-/

open Matrix Complex Polynomial SimpleGraph

namespace Chem

/-- The primitive eighth root of unity `exp (2πi/8) = (√2/2)(1 + i)`. -/

lemma eig_entry (k : ℕ) (hk : k < 8) :
    om ^ k + om ^ (7 * k) = ((2 * Real.cos (2 * Real.pi * k / 8) : ℝ) : ℂ) := by
  interval_cases k
  · rw [show (2 * Real.pi * ((0:ℕ):ℝ) / 8 : ℝ) = 0 by push_cast; ring, Real.cos_zero]
    norm_num
  · rw [show (2 * Real.pi * ((1:ℕ):ℝ) / 8 : ℝ) = Real.pi / 4 by push_cast; ring,
      Real.cos_pi_div_four]
    rw [show (7 * 1 : ℕ) = 7 from rfl, om7, pow_one, om]
    push_cast
    apply Complex.ext <;> (simp; try ring)
  · rw [show (2 * Real.pi * ((2:ℕ):ℝ) / 8 : ℝ) = Real.pi / 2 by push_cast; ring,
      Real.cos_pi_div_two]
    rw [show (7 * 2 : ℕ) = 14 from rfl, om_reduce 14 6 1 rfl, om6, om_sq]
    norm_num
  · rw [show (2 * Real.pi * ((3:ℕ):ℝ) / 8 : ℝ) = Real.pi - Real.pi / 4 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
    rw [show (7 * 3 : ℕ) = 21 from rfl, om_reduce 21 5 2 rfl, om5, om3, om]
    push_cast
    apply Complex.ext <;> (simp; try ring)
  · rw [show (2 * Real.pi * ((4:ℕ):ℝ) / 8 : ℝ) = Real.pi by push_cast; ring, Real.cos_pi]
    rw [show (7 * 4 : ℕ) = 28 from rfl, om_reduce 28 4 3 rfl, om4]
    norm_num
  · rw [show (2 * Real.pi * ((5:ℕ):ℝ) / 8 : ℝ) = Real.pi + Real.pi / 4 by push_cast; ring,
      Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]
    rw [show (7 * 5 : ℕ) = 35 from rfl, om_reduce 35 3 4 rfl, om5, om3, om]
    push_cast
    apply Complex.ext <;> (simp; try ring)
  · rw [show (2 * Real.pi * ((6:ℕ):ℝ) / 8 : ℝ) = Real.pi + Real.pi / 2 by push_cast; ring,
      Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
    rw [show (7 * 6 : ℕ) = 42 from rfl, om_reduce 42 2 5 rfl, om6, om_sq]
    norm_num
  · rw [show (2 * Real.pi * ((7:ℕ):ℝ) / 8 : ℝ) = 2 * Real.pi - Real.pi / 4 by push_cast; ring,
      Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_four]
    rw [show (7 * 7 : ℕ) = 49 from rfl, om_reduce 49 1 6 rfl, om7, pow_one, om]
    push_cast
    apply Complex.ext <;> (simp; try ring)

/-- Complex form: the characteristic polynomial of the adjacency matrix of `C₈` factors as
`∏_{k=0}^{7} (X - 2 cos (2πk/8))`. -/
