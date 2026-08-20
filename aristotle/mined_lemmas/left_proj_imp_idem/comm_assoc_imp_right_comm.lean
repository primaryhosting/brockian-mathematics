import Mathlib

/-!
# Equational Implications over Magmas

This file proves a collection of equational implications for magmas — algebraic
structures with a single binary operation `◇` (`Magma.op`).

Every proof uses only: `intro`, `exact`, `calc`, `have`, `congrArg`, `.symm`, `.trans`.
-/

class Magma (α : Type*) where
  op : α → α → α

infixl:65 " ◇ " => Magma.op

variable {G : Type*} [Magma G]

-----------------------------------------------------------------------
-- 1. Left projection ⟹ idempotent
--    x ◇ y = x  ⟹  x ◇ x = x
-----------------------------------------------------------------------

theorem comm_assoc_imp_right_comm
    (h_comm : ∀ x y : G, x ◇ y = y ◇ x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y z : G, (x ◇ y) ◇ z = (x ◇ z) ◇ y := by
  intro x y z
  calc (x ◇ y) ◇ z
      _ = x ◇ (y ◇ z) := h_assoc x y z
      _ = x ◇ (z ◇ y) := congrArg (x ◇ ·) (h_comm y z)
      _ = (x ◇ z) ◇ y := (h_assoc x z y).symm

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

