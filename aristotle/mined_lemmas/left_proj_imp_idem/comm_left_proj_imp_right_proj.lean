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

theorem comm_left_proj_imp_right_proj
    (h_comm : ∀ x y : G, x ◇ y = y ◇ x)
    (h_left : ∀ x y : G, x ◇ y = x) :
    ∀ x y : G, x ◇ y = y := by
  intro x y
  exact (h_comm x y).trans (h_left y x)

-----------------------------------------------------------------------
-- 12. Commutative + associative ⟹ left‑commutativity
--     x ◇ y = y ◇ x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z)
--     ⟹  x ◇ (y ◇ z) = y ◇ (x ◇ z)
-----------------------------------------------------------------------
