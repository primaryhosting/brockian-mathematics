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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann
namespace Redheffer

/-- The 5×5 Redheffer matrix over `ℤ` (0-indexed): entry `(i, j)` is `1` when `j = 0`
or when `i + 1` divides `j + 1`, and `0` otherwise. -/
def R5 : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- Explicit entries of the 5×5 Redheffer matrix. -/
theorem R5_eq :
    R5 = !![1, 1, 1, 1, 1;
            1, 1, 0, 1, 0;
            1, 0, 1, 0, 0;
            1, 0, 0, 1, 0;
            1, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R5]

set_option maxRecDepth 100000 in
/-- The determinant of the 5×5 Redheffer matrix equals the Mertens function value
`M(5) = -2`. -/
theorem det_eq_mertens_5 : R5.det = -2 := by
  rw [R5_eq]
  decide

/-- The Mertens function at `5`: `mu 1 + mu 2 + mu 3 + mu 4 + mu 5 = 1 - 1 - 1 + 0 - 1 = -2`. -/
theorem mertens_five : ∑ n ∈ Finset.Icc 1 5, ArithmeticFunction.moebius n = -2 := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  simp [Finset.sum_Icc_succ_top, h2, h3, h4, h5]

/-- The determinant of the 5×5 Redheffer matrix equals the Mertens function `M(5)`. -/
theorem det_R5_eq_mertens :
    R5.det = ∑ n ∈ Finset.Icc 1 5, ArithmeticFunction.moebius n := by
  rw [det_eq_mertens_5, mertens_five]

#print axioms det_eq_mertens_5

end Redheffer
end Riemann

