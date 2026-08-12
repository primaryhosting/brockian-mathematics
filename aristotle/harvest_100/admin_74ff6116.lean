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

/-
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

open Matrix

/-- The `6 × 6` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/
def R6 : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ (i : ℕ) + 1 ∣ (j : ℕ) + 1 then 1 else 0

/-- Explicit entries of the `6 × 6` Redheffer matrix. -/
lemma R6_eq :
    R6 = !![1,1,1,1,1,1;
            1,1,0,1,0,1;
            1,0,1,0,0,1;
            1,0,0,1,0,0;
            1,0,0,0,1,0;
            1,0,0,0,0,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R6]

/-- The Mertens function at `6`, i.e. `∑_{n = 1}^{6} μ(n)`, equals `-1`. -/
lemma mertens_six :
    ∑ n ∈ Finset.Icc 1 6, (ArithmeticFunction.moebius n : ℤ) = -1 := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h4 : ArithmeticFunction.moebius 4 = 0 := by decide
  have h5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h6 : ArithmeticFunction.moebius 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num), h2, h3]
    norm_num
  rw [show (Finset.Icc 1 6 : Finset ℕ) = {1, 2, 3, 4, 5, 6} from rfl]
  norm_num [h2, h3, h4, h5, h6]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Redheffer's determinant identity at `n = 6`.**
The determinant of the `6 × 6` Redheffer matrix equals `M(6) = ∑_{n ≤ 6} μ(n) = -1`. -/
theorem det_eq_mertens_6 : R6.det = -1 := by
  rw [R6_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- The determinant of the `6 × 6` Redheffer matrix equals the Mertens function `M(6)`. -/
theorem det_R6_eq_mertens_sum :
    R6.det = ∑ n ∈ Finset.Icc 1 6, (ArithmeticFunction.moebius n : ℤ) := by
  rw [det_eq_mertens_6, mertens_six]

/-- The Mertens value splits as `M(6) = M(5) + μ(6) = -2 + 1 = -1`. -/
theorem det_R6_eq_mertens_five_add_moebius_six :
    R6.det = (∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ))
      + ArithmeticFunction.moebius 6 ∧
    (∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ)) = -2 ∧
    ArithmeticFunction.moebius 6 = 1 := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h4 : ArithmeticFunction.moebius 4 = 0 := by decide
  have h5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h6 : ArithmeticFunction.moebius 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num), h2, h3]
    norm_num
  have hM5 : (∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ)) = -2 := by
    rw [show (Finset.Icc 1 5 : Finset ℕ) = {1, 2, 3, 4, 5} from rfl]
    norm_num [h2, h3, h4, h5]
  exact ⟨by rw [det_eq_mertens_6, hM5, h6]; norm_num, hM5, h6⟩

end Riemann.Redheffer

