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

theorem right_proj_imp_right_absorb
    (h : ∀ x y : G, x ◇ y = y) : ∀ x y : G, (x ◇ y) ◇ y = x ◇ y := by
  intro x y
  exact (h (x ◇ y) y).trans (h x y).symm

-----------------------------------------------------------------------
-- 5. Idempotent + associative ⟹ left self‑absorption
--    x ◇ x = x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z)  ⟹  x ◇ (x ◇ y) = x ◇ y
-----------------------------------------------------------------------
