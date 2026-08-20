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

namespace QC

open Complex

/-- The primitive `n`-th root of unity `exp (2πi / n)` used by the discrete Fourier transform. -/

lemma omega_inv_pow_mul (n a b c : ℕ) :
    ((omega n)⁻¹) ^ (a * b) * omega n ^ (a * c) = (omega n ^ ((c : ℤ) - (b : ℤ))) ^ a := by
  have hne : omega n ≠ 0 := omega_ne_zero n
  rw [inv_pow, ← zpow_natCast (omega n) (a * b), ← zpow_natCast (omega n) (a * c),
    ← zpow_natCast (omega n ^ ((c : ℤ) - (b : ℤ))) a, ← zpow_neg, ← zpow_add₀ hne, ← zpow_mul]
  congr 1
  push_cast
  ring

/-- The geometric sum of the powers of `ω^d` vanishes when `n` does not divide `d`. -/
