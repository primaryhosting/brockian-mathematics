import Mathlib

class Magma (α : Type*) where
  op : α → α → α

infixl:65 " ◇ " => Magma.op

/-- If x ◇ x = x (idempotent) for all x, then (x ◇ x) ◇ (x ◇ x) = x for all x. -/

theorem idemp_implies_double_idemp {α : Type*} [Magma α]
    (h : ∀ x : α, x ◇ x = x) :
    ∀ x : α, (x ◇ x) ◇ (x ◇ x) = x := by
  intro x
  exact (h (x ◇ x)).trans (h x)

/-- If x ◇ y = x (left projection) for all x y, then x ◇ (y ◇ x) = x for all x y. -/
