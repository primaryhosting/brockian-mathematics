import Mathlib

/-!
# Two Squares 113 — via Mathlib's Fermat two-square theorem

Companion to `RequestProject/TwoSquares113.lean`: the same statement obtained from the
existing Mathlib lemma `Nat.Prime.sq_add_sq`.
-/

namespace Math

/-- `113` is prime. -/

theorem prime_113 : Nat.Prime 113 := by norm_num

/-- Existence of a two-square representation of `113` from `Nat.Prime.sq_add_sq`. -/
