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

theorem apProd_le (a b m : ℕ) : apProd a b m ≤ (a + m * b) ^ m := by
  have h : apProd a b m ≤ ∏ _i ∈ Finset.Icc 1 m, (a + m * b) := by
    refine Finset.prod_le_prod' ?_
    intro i hi
    simp only [Finset.mem_Icc] at hi
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.2) _
  simpa [Nat.card_Icc] using h

