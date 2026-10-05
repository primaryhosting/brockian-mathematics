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
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem diophFn_choose {f g : (α → ℕ) → ℕ} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => (f v).choose (g v) := by
  have du : DiophFn fun v => 2 ^ f v + 1 :=
    diophFn_add (diophFn_pow (diophFn_const 2) df) (diophFn_const 1)
  have key : DiophFn fun v => (((2 ^ f v + 1) + 1) ^ f v / (2 ^ f v + 1) ^ g v) % (2 ^ f v + 1) :=
    diophFn_mod (diophFn_div (diophFn_pow (diophFn_add du (diophFn_const 1)) df)
      (diophFn_pow du dg)) du
  exact DiophFn.congr key fun v => (choose_eq_digit (f v) (g v) (2 ^ f v + 1) (by omega)).symm

/-! ### Factorials -/

/-- An explicit form of the estimate `r(r-1)⋯(r-n+1) ≥ r^n - n^2 r^(n-1)`. -/
