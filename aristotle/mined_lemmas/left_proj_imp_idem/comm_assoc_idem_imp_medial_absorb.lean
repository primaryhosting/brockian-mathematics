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

theorem comm_assoc_idem_imp_medial_absorb
    (h_comm : ∀ x y : G, x ◇ y = y ◇ x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z))
    (h_idem : ∀ x : G, x ◇ x = x) :
    ∀ x y : G, (x ◇ y) ◇ x = x ◇ y := by
  intro x y
  calc (x ◇ y) ◇ x
      _ = x ◇ (y ◇ x) := h_assoc x y x
      _ = x ◇ (x ◇ y) := congrArg (x ◇ ·) (h_comm y x)
      _ = (x ◇ x) ◇ y := (h_assoc x x y).symm
      _ = x ◇ y        := congrArg (· ◇ y) (h_idem x)

-----------------------------------------------------------------------
-- 14. Associative ⟹ power‑associativity identity
--     (x ◇ y) ◇ z = x ◇ (y ◇ z)
--     ⟹  ((x ◇ y) ◇ z) ◇ w = x ◇ (y ◇ (z ◇ w))
-----------------------------------------------------------------------
