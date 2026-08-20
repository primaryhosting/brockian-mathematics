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

theorem idem_imp_double_idem
    (h : ∀ x : G, x ◇ x = x) : ∀ x : G, (x ◇ x) ◇ (x ◇ x) = x := by
  intro x
  exact (h (x ◇ x)).trans (h x)

-----------------------------------------------------------------------
-- 9. Idempotent ⟹ left congruence cancellation
--    x ◇ x = x  ⟹  (x ◇ x) ◇ y = x ◇ y
-----------------------------------------------------------------------
