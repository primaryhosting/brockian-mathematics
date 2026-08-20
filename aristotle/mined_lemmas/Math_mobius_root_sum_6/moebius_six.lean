/-
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mobius Root Sum 6
Category: Pure Mathematics
Target: Math.mobius_root_sum_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- The Möbius function at `6` equals `1` (since `6 = 2 * 3` is squarefree with two prime
factors). -/

theorem moebius_six : ArithmeticFunction.moebius 6 = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree (by decide +kernel),
    ArithmeticFunction.cardFactors_apply,
    show Nat.primeFactorsList 6 = [2, 3] from by decide +kernel]
  norm_num

/-- A primitive `6`-th root of unity in `ℂ` is a root of the sixth cyclotomic polynomial
`X ^ 2 - X + 1`. -/
