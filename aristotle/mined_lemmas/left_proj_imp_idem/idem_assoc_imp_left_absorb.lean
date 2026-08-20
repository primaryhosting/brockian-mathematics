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

theorem idem_assoc_imp_left_absorb
    (h_idem : ∀ x : G, x ◇ x = x)
    (h_assoc : ∀ x y z : G, (x ◇ y) ◇ z = x ◇ (y ◇ z)) :
    ∀ x y : G, x ◇ (x ◇ y) = x ◇ y := by
  intro x y
  exact (h_assoc x x y).symm.trans (congrArg (· ◇ y) (h_idem x))

-----------------------------------------------------------------------
-- 6. Idempotent + associative ⟹ right self‑absorption
--    x ◇ x = x ∧ (x ◇ y) ◇ z = x ◇ (y ◇ z)  ⟹  (x ◇ y) ◇ y = x ◇ y
-----------------------------------------------------------------------
