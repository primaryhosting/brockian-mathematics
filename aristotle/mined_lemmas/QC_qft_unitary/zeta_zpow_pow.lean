import Mathlib

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

/-
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Qft Unitary
Category: Quantum Computing
Target: QC.qft_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex Finset

/-- The primitive `N`-th root of unity `exp (2 π i / N)`. -/

lemma zeta_zpow_pow {N : ℕ} (j l k : Fin N) :
    ((zeta N) ^ ((j.val : ℤ) - (l.val : ℤ))) ^ k.val
      = zeta N ^ (j.val * k.val) * (zeta N ^ (l.val * k.val))⁻¹ := by
  rw [← zpow_natCast (zeta N ^ _) k.val, ← zpow_mul, sub_mul, zpow_sub₀ (zeta_ne_zero N),
    div_eq_mul_inv]
  norm_cast

/-- The `(j, l)` term of the product `dftMatrix N * (dftMatrix N)ᴴ`. -/
