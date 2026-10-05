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

lemma succ_ne_pred (hn : 3 ≤ n) (i : Fin n) : (i + 1 : Fin n) ≠ i - 1 := by
  intro h
  have h2 : ((1 : Fin n) + 1 : Fin n) = 0 := by
    have : (i + 1 : Fin n) - (i - 1) = 0 := by rw [h, sub_self]
    calc ((1 : Fin n) + 1 : Fin n) = (i + 1 : Fin n) - (i - 1) := by abel
      _ = 0 := this
  have hv : (((1 : Fin n) + 1 : Fin n) : ℕ) = 2 := by
    rw [Fin.val_add, val_one_eq (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h2] at hv
  simp at hv

