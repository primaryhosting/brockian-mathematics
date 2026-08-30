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
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

/-- The 3×3 Redheffer matrix (0-indexed): `R i j = 1` when `j = 0` or `(i+1) ∣ (j+1)`,
and `0` otherwise. -/
def R : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the 3×3 Redheffer matrix equals the Mertens function
`M(3) = μ(1) + μ(2) + μ(3) = 1 - 1 - 1 = -1`. -/
theorem det_eq_mertens_3 : R.det = -1 := by
  rw [Matrix.det_fin_three]
  simp only [R, Matrix.of_apply]
  decide

/-- The Mertens function at 3, `∑_{k=1}^{3} μ(k) = -1`, matching `det R`. -/
theorem mertens_three : ∑ k ∈ Finset.Icc 1 3, (ArithmeticFunction.moebius k : ℤ) = -1 := by
  rw [show Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]
  simp [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]

/-- `det R = M(3)`, the Redheffer determinant identity at `n = 3`. -/
theorem det_eq_mertens_sum :
    R.det = ∑ k ∈ Finset.Icc 1 3, (ArithmeticFunction.moebius k : ℤ) := by
  rw [det_eq_mertens_3, mertens_three]

end Riemann.Redheffer

