import Mathlib

/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann.Redheffer

/-- The `6 × 6` Redheffer matrix: `R i j = 1` if `j = 0` (first column) or if
`i + 1` divides `j + 1` (using the `0`-indexed `Fin 6` entries), and `0` otherwise. -/
def R6 : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => if j.val = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0

/-- Explicit entries of the `6 × 6` Redheffer matrix. -/
lemma R6_eq :
    R6 = !![1, 1, 1, 1, 1, 1;
            1, 1, 0, 1, 0, 1;
            1, 0, 1, 0, 0, 1;
            1, 0, 0, 1, 0, 0;
            1, 0, 0, 0, 1, 0;
            1, 0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [R6]

/-- The determinant of the `6 × 6` Redheffer matrix equals `-1`, which is the value
`M(6) = ∑_{k = 1}^{6} μ(k)` of the Mertens function at `6`. -/
theorem det_eq_mertens_6 : Matrix.det R6 = -1 := by
  rw [R6_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- The Mertens function at `6`, i.e. `∑_{k = 1}^{6} μ(k)`, equals `-1`. -/
lemma mertens_6 :
    ∑ k ∈ Finset.Icc 1 6, (ArithmeticFunction.moebius k : ℤ) = -1 := by
  have h1 : ArithmeticFunction.moebius 1 = 1 := by simp
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  have h5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have h6 : ArithmeticFunction.moebius 6 = 1 := by
    have hmul := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (show Nat.Coprime 2 3 by decide)
    simpa [h2, h3] using hmul
  rw [show (Finset.Icc 1 6 : Finset ℕ) = {1, 2, 3, 4, 5, 6} from rfl]
  norm_num [h1, h2, h3, h4, h5, h6]

/-- The determinant of the `6 × 6` Redheffer matrix agrees with the Mertens function
at `6`. -/
theorem det_R6_eq_mertens :
    Matrix.det R6 = ∑ k ∈ Finset.Icc 1 6, (ArithmeticFunction.moebius k : ℤ) := by
  rw [det_eq_mertens_6, mertens_6]

end Riemann.Redheffer

