/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

/-- The `4 × 4` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`,
and `R i j = 0` otherwise (the `Fin 4` indices `0,1,2,3` stand for `1,2,3,4`). -/
def R4 : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => if j = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0

/-- Explicit entries of the `4 × 4` Redheffer matrix. -/
theorem R4_eq : R4 = !![1, 1, 1, 1; 1, 1, 0, 1; 1, 0, 1, 0; 1, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The Mertens function `M(n) = ∑_{k=1}^{n} μ(k)`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k

theorem moebius_four : ArithmeticFunction.moebius 4 = 0 := by
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
  decide

/-- `M(4) = μ(1) + μ(2) + μ(3) + μ(4) = 1 - 1 - 1 + 0 = -1`. -/
theorem mertens_four : mertens 4 = -1 := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  simp [mertens, Finset.sum_Icc_succ_top, h2, h3, moebius_four]

/-- The determinant of the `4 × 4` Redheffer matrix is `-1`, which equals the Mertens
function value `M(4) = μ(1) + μ(2) + μ(3) + μ(4) = -1`. -/
theorem det_eq_mertens_4 : R4.det = -1 ∧ R4.det = mertens 4 := by
  have hdet : R4.det = -1 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply, R4, Fin.succAbove]
  exact ⟨hdet, by rw [hdet, mertens_four]⟩

end Riemann.Redheffer

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

