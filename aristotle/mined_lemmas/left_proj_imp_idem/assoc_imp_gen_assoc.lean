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

theorem assoc_imp_gen_assoc
    (h : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y z w : G, ((x ◇ y) ◇ z) ◇ w = x ◇ (y ◇ (z ◇ w)) := by
  intro x y z w
  calc ((x ◇ y) ◇ z) ◇ w
      _ = (x ◇ y) ◇ (z ◇ w) := h (x ◇ y) z w
      _ = x ◇ (y ◇ (z ◇ w)) := h x y (z ◇ w)

-----------------------------------------------------------------------
-- 15. Commutative + associative ⟹ right‑commutativity
--     x ◇ y = y ◇ x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z)
--     ⟹  (x ◇ y) ◇ z = (x ◇ z) ◇ y
-----------------------------------------------------------------------
