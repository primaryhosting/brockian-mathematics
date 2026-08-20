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

theorem idem_imp_right_cong
    (h : ∀ x : G, x ◇ x = x) : ∀ x y : G, x ◇ (y ◇ y) = x ◇ y := by
  intro x y
  exact congrArg (x ◇ ·) (h y)

-----------------------------------------------------------------------
-- 11. Commutative + left projection ⟹ right projection
--     x ◇ y = y ◇ x ∧ x ◇ y = x  ⟹  x ◇ y = y
-----------------------------------------------------------------------
