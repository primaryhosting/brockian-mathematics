import Mathlib

/-!
# Det Eq Mertens 3
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

/-- The 3×3 Redheffer matrix: `R i j = 1` when `j = 0` or `(i+1) ∣ (j+1)`
(with `0`-indexed `Fin 3` indices), and `0` otherwise. -/

def R : Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the 3×3 Redheffer matrix equals the Mertens function
`M 3 = μ 1 + μ 2 + μ 3 = 1 - 1 - 1 = -1`. -/

theorem det_eq_mertens_3 : R.det = -1 := by
  rw [Matrix.det_fin_three]
  norm_num [R, Fin.ext_iff]

/-- The Mertens function at `3`: `M 3 = μ 1 + μ 2 + μ 3 = -1`. -/
