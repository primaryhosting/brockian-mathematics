import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
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

namespace QC

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma omega_zpow_sub (N j k l : ℕ) :
    ((omega N)⁻¹) ^ (k * j) * (omega N) ^ (k * l)
      = ((omega N) ^ ((l : ℤ) - (j : ℤ))) ^ k := by
  have h0 : omega N ≠ 0 := omega_ne_zero N
  have hinv : ((omega N)⁻¹) ^ (k * j) = (omega N) ^ (-((k * j : ℕ) : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hinv, ← zpow_natCast (omega N) (k * l), ← zpow_add₀ h0,
    ← zpow_natCast ((omega N) ^ ((l : ℤ) - (j : ℤ))) k, ← zpow_mul]
  congr 1
  push_cast
  ring

