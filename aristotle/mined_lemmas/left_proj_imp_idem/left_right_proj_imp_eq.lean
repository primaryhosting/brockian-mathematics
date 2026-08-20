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

theorem left_right_proj_imp_eq
    (h1 : ∀ x y : G, x ◇ y = x)
    (h2 : ∀ x y : G, x ◇ y = y) :
    ∀ x y : G, x = y := by
  intro x y
  exact (h1 x y).symm.trans (h2 x y)

-----------------------------------------------------------------------
-- 8. Idempotent ⟹ double‑idempotent
--    x ◇ x = x  ⟹  (x ◇ x) ◇ (x ◇ x) = x
-----------------------------------------------------------------------
