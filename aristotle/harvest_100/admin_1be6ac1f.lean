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
# Nat Cast Add
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.natCast_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Ordinal

universe u

/-- Casting a sum of naturals into the ordinals agrees with ordinal addition. -/
theorem natCast_add (m n : ℕ) :
    ((m + n : ℕ) : Ordinal.{u}) = (m : Ordinal.{u}) + (n : Ordinal.{u}) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1 : ((m + k + 1 : ℕ) : Ordinal.{u}) = ((m + k : ℕ) : Ordinal.{u}) + 1 :=
        Nat.cast_succ (R := Ordinal.{u}) (m + k)
      have h2 : ((k + 1 : ℕ) : Ordinal.{u}) = (k : Ordinal.{u}) + 1 :=
        Nat.cast_succ (R := Ordinal.{u}) k
      calc ((m + (k + 1) : ℕ) : Ordinal.{u}) = ((m + k + 1 : ℕ) : Ordinal.{u}) := by
            rw [Nat.add_assoc]
        _ = ((m + k : ℕ) : Ordinal.{u}) + 1 := h1
        _ = ((m : Ordinal.{u}) + (k : Ordinal.{u})) + 1 := by rw [ih]
        _ = (m : Ordinal.{u}) + ((k : Ordinal.{u}) + 1) := add_assoc _ _ _
        _ = (m : Ordinal.{u}) + ((k + 1 : ℕ) : Ordinal.{u}) := by rw [h2]

/-- Casting a product of naturals into the ordinals agrees with ordinal multiplication. -/
theorem natCast_mul' (m n : ℕ) :
    ((m * n : ℕ) : Ordinal.{u}) = (m : Ordinal.{u}) * (n : Ordinal.{u}) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h : (m * (k + 1) : ℕ) = m * k + m := by ring
      rw [h, natCast_add, ih, Nat.cast_succ, mul_add, mul_one]

end Ordinal

