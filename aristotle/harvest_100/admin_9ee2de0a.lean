import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

/-- The `n × n` Redheffer matrix: entry `(i, j)` is `1` when `j = 0` (first column)
or when `i + 1` divides `j + 1` (using `1`-based indices), and `0` otherwise. -/
def redheffer (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.moebius k : ℤ)

/-- The determinant of the `4 × 4` Redheffer matrix equals
`M 4 = μ 1 + μ 2 + μ 3 + μ 4 = 1 - 1 - 1 + 0 = -1`. -/
theorem det_eq_mertens_4 : (redheffer 4).det = -1 ∧ mertens 4 = -1 := by
  constructor
  · have hR : redheffer 4 = !![1, 1, 1, 1; 1, 1, 0, 1; 1, 0, 1, 0; 1, 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [redheffer]
    rw [hR]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    decide
  · have h1 : (ArithmeticFunction.moebius 1 : ℤ) = 1 := by simp
    have h2 : (ArithmeticFunction.moebius 2 : ℤ) = -1 := by
      rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
    have h3 : (ArithmeticFunction.moebius 3 : ℤ) = -1 := by
      rw [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
    have h4 : (ArithmeticFunction.moebius 4 : ℤ) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
      decide
    simp [mertens, show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl, h1, h2, h3, h4]

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

