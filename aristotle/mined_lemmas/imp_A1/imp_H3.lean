import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/


theorem imp_H3 (h : ∀ x y : G, x * (x * y) = x * y) :
    ∀ x y z : G, (x * y) * ((x * y) * z) = (x * y) * z := by
  intro x y z; exact h (x * y) z

/-! ## Section I: From right self-idempotency (∀ x y, (x * y) * y = x * y) — 3 theorems -/

