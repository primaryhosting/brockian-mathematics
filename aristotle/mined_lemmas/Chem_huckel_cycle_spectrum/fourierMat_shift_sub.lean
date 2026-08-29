import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Matrix Complex

/-! ## The `n`-th root of unity and its basic arithmetic -/

section Roots

variable (n : ℕ) [NeZero n]

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma fourierMat_shift_sub (hn : 2 ≤ n) (i k : Fin n) :
    fourierMat n (i - 1) k = fourierMat n i k * ((zeta n) ^ (k : ℕ))⁻¹ := by
  have hz : ((zeta n) ^ (k : ℕ)) ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
  rw [eq_mul_inv_iff_mul_eq₀ hz]
  simp only [fourierMat, Matrix.of_apply]
  rw [← pow_add]
  refine zeta_pow_modEq ?_
  have h : Nat.ModEq n (((i - 1 : Fin n) : ℕ) + 1) (i : ℕ) := by
    have := val_sub_add_modEq i (1 : Fin n)
    rwa [val_one_eq hn] at this
  calc ((i - 1 : Fin n) : ℕ) * (k : ℕ) + (k : ℕ)
      = (((i - 1 : Fin n) : ℕ) + 1) * (k : ℕ) := by ring
    _ ≡ (i : ℕ) * (k : ℕ) [MOD n] := h.mul_right _

