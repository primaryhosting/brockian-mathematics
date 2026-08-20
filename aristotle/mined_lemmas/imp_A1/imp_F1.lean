import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/


theorem imp_F1
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_i : ∀ x : G, x * x = x) :
    ∀ x y : G, x * (x * y) = x * y := by
  intro x y
  exact (h_a x x y).symm.trans (congrArg (· * y) (h_i x))

