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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


namespace Riemann.Redheffer

/-- The 5×5 Redheffer matrix over `ℤ` (0-indexed): `R i j = 1` if `j = 0` or
`(i+1) ∣ (j+1)`, and `0` otherwise. -/
def R : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the 5×5 Redheffer matrix equals the Mertens function value
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1 = -2`. -/
theorem det_eq_mertens_5 : R.det = -2 := by
  simp [R, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- The Mertens function at 5, `∑_{n=1}^{5} μ(n)`, equals `-2`. -/
theorem mertens_5 : ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n) = -2 := by
  have h1 : ArithmeticFunction.moebius 1 = 1 := by simp
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h4 : ArithmeticFunction.moebius 4 = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    decide
  have h5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  rw [show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    h1, h2, h3, h4, h5]
  norm_num

/-- `det R = M(5)`. -/
theorem det_eq_mertens_5' :
    R.det = ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n) := by
  rw [det_eq_mertens_5, mertens_5]

end Riemann.Redheffer

