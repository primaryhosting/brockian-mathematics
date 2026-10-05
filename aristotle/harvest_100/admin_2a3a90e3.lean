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

/-- The 3×3 Redheffer matrix: `R i j = 1` when `j = 0` or `(i+1) ∣ (j+1)`
(with `Fin 3` indices read as `0,1,2`), and `0` otherwise. -/
def R3 : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the `3 × 3` Redheffer matrix equals the Mertens function
`M 3 = μ 1 + μ 2 + μ 3 = -1`. -/
theorem det_eq_mertens_3 : R3.det = -1 := by
  rw [Matrix.det_fin_three]
  norm_num [R3, Matrix.of_apply, Fin.isValue]
  decide

end Redheffer
end Riemann

