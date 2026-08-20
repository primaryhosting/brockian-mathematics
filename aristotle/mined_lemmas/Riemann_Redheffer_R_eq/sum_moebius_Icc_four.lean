import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

open ArithmeticFunction

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` (first column) or if
`(i+1) ∣ (j+1)` (divisibility of the 1-based indices), and `0` otherwise. -/

theorem sum_moebius_Icc_four : ∑ n ∈ Finset.Icc 1 4, (moebius n : ℤ) = -1 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (moebius 2 : ℤ) = -1 from moebius_apply_prime (by norm_num),
      show (moebius 3 : ℤ) = -1 from moebius_apply_prime (by norm_num),
      show (moebius 4 : ℤ) = 0 by decide, moebius_apply_one]
  norm_num

/-- The determinant of the 4×4 Redheffer matrix is the sum of the values of the
Möbius function at `1, 2, 3, 4`, i.e. the Mertens function `M(4)`. -/
