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

theorem left_proj_imp_left_absorb
    (h : ∀ x y : G, x ◇ y = x) : ∀ x y : G, x ◇ (x ◇ y) = x ◇ y := by
  intro x y
  exact (h x (x ◇ y)).trans (h x y).symm

-----------------------------------------------------------------------
-- 4. Right projection ⟹ right self‑absorption
--    x ◇ y = y  ⟹  (x ◇ y) ◇ y = x ◇ y
-----------------------------------------------------------------------
