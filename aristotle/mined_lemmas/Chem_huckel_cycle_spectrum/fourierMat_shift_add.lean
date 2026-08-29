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

lemma fourierMat_shift_add (hn : 2 ≤ n) (i k : Fin n) :
    fourierMat n (i + 1) k = fourierMat n i k * (zeta n) ^ (k : ℕ) := by
  simp only [fourierMat, Matrix.of_apply]
  rw [← pow_add]
  refine zeta_pow_modEq ?_
  have h : Nat.ModEq n ((i + 1 : Fin n) : ℕ) ((i : ℕ) + 1) := by
    have := val_add_modEq i (1 : Fin n)
    rwa [val_one_eq hn] at this
  calc ((i + 1 : Fin n) : ℕ) * (k : ℕ) ≡ ((i : ℕ) + 1) * (k : ℕ) [MOD n] := h.mul_right _
    _ = (i : ℕ) * (k : ℕ) + (k : ℕ) := by ring

