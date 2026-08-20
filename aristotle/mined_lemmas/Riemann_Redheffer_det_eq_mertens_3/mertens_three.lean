import Mathlib

/-!
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
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

/-- The 3×3 Redheffer matrix (0-indexed): entry `(i, j)` is `1` when `j = 0`
or when `i + 1` divides `j + 1`, and `0` otherwise. -/

theorem mertens_three : ∑ n ∈ Finset.Icc 1 3, (ArithmeticFunction.moebius n : ℤ) = -1 := by
  have h : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := rfl
  rw [h]
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three]

/-- `det R = -1 = M 3`, the Redheffer determinant identity at `n = 3`. -/
