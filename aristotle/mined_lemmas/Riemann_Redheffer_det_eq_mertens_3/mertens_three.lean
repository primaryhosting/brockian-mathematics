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

theorem mertens_three : (∑ n ∈ Finset.Icc 1 3, ArithmeticFunction.moebius n) = -1 := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  simp [Finset.sum_Icc_succ_top, h2, h3]

/-- `det R₃ = M 3`, the base case of the Redheffer determinant identity. -/
