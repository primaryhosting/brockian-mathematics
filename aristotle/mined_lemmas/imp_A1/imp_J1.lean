import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/


theorem imp_J1
    (h_c : ∀ x y : G, x * y = y * x)
    (h_l : ∀ x y : G, x * (x * y) = x * y) :
    ∀ x y : G, (x * y) * y = x * y := by
  intro x y
  calc (x * y) * y
      = y * (x * y) := h_c (x * y) y
    _ = y * (y * x) := congrArg (y * ·) (h_c x y)
    _ = y * x       := h_l y x
    _ = x * y       := h_c y x

