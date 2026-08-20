/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Riemann.Redheffer

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, else `0`. -/
def R4 : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function `M(n) = ∑_{k=1}^{n} μ(k)`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k

/-- Explicit entries of the 4×4 Redheffer matrix. -/
theorem R4_eq : R4 = !![1, 1, 1, 1; 1, 1, 0, 1; 1, 0, 1, 0; 1, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [R4]

/-- `M(4) = μ(1) + μ(2) + μ(3) + μ(4) = 1 - 1 - 1 + 0 = -1`. -/
theorem mertens_four : mertens 4 = -1 := by
  rw [mertens, show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  simp [ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide : ¬ Squarefree 4)]

/-- The determinant of the 4×4 Redheffer matrix is `-1`, which equals the Mertens
function value `M(4)`. -/
theorem det_eq_mertens_4 : R4.det = -1 ∧ R4.det = mertens 4 := by
  have hdet : R4.det = -1 := by rw [R4_eq]; decide
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

