import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
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

open scoped Matrix

/-! ### A primitive 14-th root of unity and the associated character -/

/-- A primitive 14-th root of unity. -/

theorem Fm_succ (j l : Fin 14) : Fm (j + 1) l = Fm j l * ee ((l : ℕ) : ℤ) := by
  have hc := fin_val_add_cong j 1
  have h1 : (((1 : Fin 14) : ℕ) : ℤ) = 1 := by norm_num
  rw [h1] at hc
  have : (((j + 1 : Fin 14) : ℕ) : ℤ) * ((l : ℕ) : ℤ)
      ≡ (((j : ℕ) : ℤ) + 1) * ((l : ℕ) : ℤ) [ZMOD 14] := Int.ModEq.mul_right _ hc
  rw [Fm, ee_congr this,
    show (((j : ℕ) : ℤ) + 1) * ((l : ℕ) : ℤ)
      = ((j : ℕ) : ℤ) * ((l : ℕ) : ℤ) + ((l : ℕ) : ℤ) by ring, ee_add]
  rfl

