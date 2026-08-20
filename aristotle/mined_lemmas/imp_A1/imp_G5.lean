import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/


theorem imp_G5
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y z : G, x * (y * z) = (z * x) * y := by
  intro x y z
  calc x * (y * z)
      = x * (z * y) := congrArg (x * ·) (h_c y z)
    _ = (x * z) * y := (h_a x z y).symm
    _ = (z * x) * y := congrArg (· * y) (h_c x z)

/-! ## Section H: From left self-idempotency (∀ x y, x * (x * y) = x * y) — 3 theorems -/

