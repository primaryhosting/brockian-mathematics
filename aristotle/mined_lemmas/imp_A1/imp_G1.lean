import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/


theorem imp_G1
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_c : ∀ x y : G, x * y = y * x) :
    ∀ x y z : G, x * (y * z) = y * (x * z) := by
  intro x y z
  exact ((h_a x y z).symm.trans (congrArg (· * z) (h_c x y))).trans (h_a y x z)

