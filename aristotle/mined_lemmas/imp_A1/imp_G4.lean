import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/


theorem imp_G4
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y z w : G, (x * y) * (z * w) = (x * z) * (y * w) := by
  intro x y z w
  calc (x * y) * (z * w)
      = x * (y * (z * w)) := h_a x y (z * w)
    _ = x * ((y * z) * w) := congrArg (x * ·) (h_a y z w).symm
    _ = x * ((z * y) * w) := congrArg (x * ·) (congrArg (· * w) (h_c y z))
    _ = x * (z * (y * w)) := congrArg (x * ·) (h_a z y w)
    _ = (x * z) * (y * w) := (h_a x z (y * w)).symm

