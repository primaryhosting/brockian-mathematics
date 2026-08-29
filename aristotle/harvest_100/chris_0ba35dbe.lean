import Mathlib

/-!
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The `3 × 3` Redheffer matrix: `R i j = 1` when `j = 0` (0-indexed first column)
or when `i + 1` divides `j + 1`, and `0` otherwise. -/
def R : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0

/-- The Mertens function `M(n) = ∑_{k ≤ n} μ(k)`, here at `n = 3`:
`M(3) = μ(1) + μ(2) + μ(3) = 1 - 1 - 1 = -1`. -/
theorem mertens_three :
    ∑ k ∈ Finset.Icc 1 3, (ArithmeticFunction.moebius k : ℤ) = -1 := by
  rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) from rfl]
  norm_num [ArithmeticFunction.moebius_apply_prime, Nat.prime_two, Nat.prime_three]

/-- The determinant of the `3 × 3` Redheffer matrix equals `M(3) = -1`. -/
theorem det_eq_mertens_3 : R.det = -1 := by
  rw [Matrix.det_fin_three]
  simp only [R, Matrix.of_apply]
  norm_num
  decide

/-- The base identity `det R_n = M(n)` at `n = 3`. -/
theorem det_eq_mertens_sum_three :
    R.det = ∑ k ∈ Finset.Icc 1 3, (ArithmeticFunction.moebius k : ℤ) := by
  rw [det_eq_mertens_3, mertens_three]

end Redheffer
end Riemann

