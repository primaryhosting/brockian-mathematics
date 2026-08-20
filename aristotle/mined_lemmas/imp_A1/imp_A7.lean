import Mathlib

set_option maxHeartbeats 8000000

variable {G : Type*} [Mul G]

/-! # 44 Equational Implications over Magmas

Each theorem proves that if a hypothesis equation holds for all elements
of a magma (G, *), then a conclusion equation also holds.
Proofs use only: intro, exact, calc, have, congrArg, .symm, .trans.
-/

/-! ## Section A: From left projection (∀ x y, x * y = x) — 7 theorems -/


theorem imp_A7 (h : ∀ x y : G, x * y = x) :
    ∀ x y z : G, x * y = x * z := by
  intro x y z; exact (h x y).trans (h x z).symm

/-! ## Section B: From right projection (∀ x y, x * y = y) — 7 theorems -/

