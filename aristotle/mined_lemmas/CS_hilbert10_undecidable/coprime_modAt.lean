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

theorem coprime_modAt {q n i j : ℕ} (hq : (n + 1).factorial ∣ q)
    (hi : i ≤ n) (hj : j ≤ n) (hne : i ≠ j) : Nat.Coprime (modAt q i) (modAt q j) := by
  rcases Nat.lt_or_ge i j with h | h
  · exact coprime_modAt_of_lt hq h hj
  · exact (coprime_modAt_of_lt hq (by omega : j < i) hi).symm

