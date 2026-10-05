/-!
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
Statement: Define the 3x3 Redheffer matrix R with R i j = 1 if (j = 0) or (i+1) divides (j+1), else 0 (0-indexed Fin 3). Prove det R = -1, which equals the Mertens function M(3) = mu(1)+mu(2)+mu(3) = 1-1-1 = -1. (RH is equivalent to det R_n = M(n) = O(n^{1/2+eps}); this is the base identity det R_n = M(n) at n=3.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Redheffer

/-- The 3×3 Redheffer matrix: `R i j = 1` when `j = 0` or `(i+1) ∣ (j+1)`
(with `0`-indexed `Fin 3` indices), and `0` otherwise. -/
def R : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the 3×3 Redheffer matrix equals the Mertens function
`M 3 = μ 1 + μ 2 + μ 3 = 1 - 1 - 1 = -1`. -/
theorem det_eq_mertens_3 : R.det = -1 := by
  rw [Matrix.det_fin_three]
  norm_num [R, Fin.ext_iff]

/-- The Mertens function at `3`: `M 3 = μ 1 + μ 2 + μ 3 = -1`. -/
theorem mertens_three : (∑ n ∈ Finset.Icc 1 3, ArithmeticFunction.moebius n) = -1 := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  simp [Finset.sum_Icc_succ_top, h2, h3]

/-- `det R₃ = M 3`, the base case of the Redheffer determinant identity. -/
theorem det_eq_mertens_three :
    R.det = ∑ n ∈ Finset.Icc 1 3, ArithmeticFunction.moebius n := by
  rw [det_eq_mertens_3, mertens_three]

end Riemann.Redheffer

