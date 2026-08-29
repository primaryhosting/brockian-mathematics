/-
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above uses a plain block comment because Lean requires `import`
-- to precede any module docstring; the docstring form is repeated below.)

import Mathlib

/-!
# Qft Unitary 4
Category: Quantum Computing
Target: QC.qft_unitary_4
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

namespace QC

/-- The primitive `N`-th root of unity `exp (2 π i / N)` used by the quantum Fourier
transform on `N` basis states. -/

lemma qft_geom_sum (N : ℕ) (hN : N ≠ 0) (d : ℤ) (hd : ¬ ((N : ℤ) ∣ d)) :
    ∑ m ∈ Finset.range N, (qftZeta N ^ d) ^ m = 0 := by
  have hprim : IsPrimitiveRoot (qftZeta N) N := Complex.isPrimitiveRoot_exp N hN
  have hne : qftZeta N ^ d ≠ 1 := fun h => hd ((hprim.zpow_eq_one_iff_dvd d).mp h)
  have hpow : (qftZeta N ^ d) ^ N = 1 := by
    rw [← zpow_natCast (qftZeta N ^ d) N, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      hprim.pow_eq_one, one_zpow]
  rw [geom_sum_eq hne, hpow, sub_self, zero_div]

