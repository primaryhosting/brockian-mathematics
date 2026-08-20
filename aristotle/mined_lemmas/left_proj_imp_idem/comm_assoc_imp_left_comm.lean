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

theorem comm_assoc_imp_left_comm
    (h_comm : ∀ x y : G, x ◇ y = y ◇ x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y z : G, x ◇ (y ◇ z) = y ◇ (x ◇ z) := by
  intro x y z
  calc x ◇ (y ◇ z)
      _ = (x ◇ y) ◇ z := (h_assoc x y z).symm
      _ = (y ◇ x) ◇ z := congrArg (· ◇ z) (h_comm x y)
      _ = y ◇ (x ◇ z) := h_assoc y x z

-----------------------------------------------------------------------
-- 13. Commutative + associative + idempotent ⟹ medial absorption
--     x ◇ y = y ◇ x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z) ∧ x ◇ x = x
--     ⟹  (x ◇ y) ◇ x = x ◇ y
-----------------------------------------------------------------------
