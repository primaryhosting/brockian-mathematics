import Mathlib

/-!
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
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

/-- The `5 × 5` Redheffer matrix over `ℤ` (0-indexed): the entry in row `i`, column `j`
is `1` when `j = 0` or when `i + 1` divides `j + 1`, and `0` otherwise. -/
def R : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => if j = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0

/-- Explicit description of the `5 × 5` Redheffer matrix. -/
lemma R_eq :
    R = !![1, 1, 1, 1, 1;
           1, 1, 0, 1, 0;
           1, 0, 1, 0, 0;
           1, 0, 0, 1, 0;
           1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R]

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = -2`. -/
theorem det_eq_mertens_5 : R.det = -2 := by
  rw [R_eq]
  decide

/-- The Mertens function value `M(5) = ∑_{n=1}^{5} μ(n) = -2`. -/
lemma mertens_5 : ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n) = -2 := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  simp [show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) from rfl, h2, h3, h4, h5]

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function `M(5)`. -/
theorem det_eq_mertens_sum_5 :
    R.det = ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n) := by
  rw [det_eq_mertens_5, mertens_5]

end Redheffer
end Riemann

