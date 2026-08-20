import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/


theorem imp_F3
    (h_a : ∀ x y z : G, (x * y) * z = x * (y * z))
    (h_i : ∀ x : G, x * x = x) :
    ∀ x : G, x * (x * x) = x := by
  intro x
  exact ((h_a x x x).symm.trans (congrArg (· * x) (h_i x))).trans (h_i x)

/-! ## Section G: From associativity + commutativity — 5 theorems -/

