import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
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

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, else `0`. -/

theorem det_eq_mertens_sum_4 :
    R4.det = ∑ k ∈ Finset.Icc 1 4, (ArithmeticFunction.moebius k : ℤ) := by
  have h2 : (ArithmeticFunction.moebius 2 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : (ArithmeticFunction.moebius 3 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h4 : (ArithmeticFunction.moebius 4 : ℤ) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [det_eq_mertens_4, show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
  norm_num [h2, h3, h4]

end Riemann.Redheffer

