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

theorem left_proj_imp_idem
    (h : ∀ x y : G, x ◇ y = x) : ∀ x : G, x ◇ x = x := by
  intro x
  exact h x x

-----------------------------------------------------------------------
-- 2. Right projection ⟹ idempotent
--    x ◇ y = y  ⟹  x ◇ x = x
-----------------------------------------------------------------------
