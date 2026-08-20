/-
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann
namespace Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ`, with rows and columns indexed by `Fin 5`
(0-indexed): the `(i, j)` entry is `1` if `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/

theorem det_eq_sum_moebius :
    R.det = ∑ k ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius k : ℤ) := by
  have h4 : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [det_eq_mertens_5, show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) from rfl]
  norm_num [ArithmeticFunction.moebius_apply_prime, h4]

end Redheffer
end Riemann

