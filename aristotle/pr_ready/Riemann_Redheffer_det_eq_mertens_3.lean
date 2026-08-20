/-!
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
Statement: Define the 3x3 Redheffer matrix R with R i j = 1 if (j = 0) or (i+1) divides (j+1), else 0 (0-indexed Fin 3). Prove det R = -1, which equals the Mertens function M(3) = mu(1)+mu(2)+mu(3) = 1-1-1 = -1. (RH is equivalent to det R_n = M(n) = O(n^{1/2+eps}); this is the base identity det R_n = M(n) at n=3.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Riemann
namespace Redheffer

/-- The 3×3 Redheffer matrix (0-indexed): entry `(i, j)` is `1` when `j = 0`
or when `i + 1` divides `j + 1`, and `0` otherwise. -/
def R : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function `M 3 = μ 1 + μ 2 + μ 3 = 1 - 1 - 1 = -1`. -/
theorem mertens_three : ∑ n ∈ Finset.Icc 1 3, (ArithmeticFunction.moebius n : ℤ) = -1 := by
  have h : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := rfl
  rw [h]
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]

/-- `det R = -1 = M 3`, the Redheffer determinant identity at `n = 3`. -/
theorem det_eq_mertens_3 : R.det = -1 := by
  rw [Matrix.det_fin_three]
  simp [R]

/-- The determinant of the 3×3 Redheffer matrix equals the Mertens function `M 3`. -/
theorem det_eq_mertens_sum_3 :
    R.det = ∑ n ∈ Finset.Icc 1 3, (ArithmeticFunction.moebius n : ℤ) := by
  rw [det_eq_mertens_3, mertens_three]

end Redheffer
end Riemann

