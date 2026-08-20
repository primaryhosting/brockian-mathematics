import Mathlib

class Magma (α : Type*) where
  op : α → α → α

infixl:65 " ◇ " => Magma.op

/-- If x ◇ x = x (idempotent) for all x, then (x ◇ x) ◇ (x ◇ x) = x for all x. -/

theorem proj_left_implies_absorb {α : Type*} [Magma α]
    (h : ∀ x y : α, x ◇ y = x) :
    ∀ x y : α, x ◇ (y ◇ x) = x := by
  intro x y
  exact h x (y ◇ x)

/-- If x ◇ y = y (right projection) for all x y, then (x ◇ y) ◇ (x ◇ y) = y for all x y. -/
