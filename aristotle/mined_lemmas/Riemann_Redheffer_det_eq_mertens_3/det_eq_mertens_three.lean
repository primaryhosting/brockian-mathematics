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

theorem det_eq_mertens_three :
    R.det = ∑ n ∈ Finset.Icc 1 3, ArithmeticFunction.moebius n := by
  rw [det_eq_mertens_3, mertens_three]

end Riemann.Redheffer

