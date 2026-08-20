import Mathlib
namespace Frontier.CryptoComplexity
open Function

/-- The one-time pad map `k ↦ m ^^^ k` is a bijection, since it is an involution. -/

theorem hash_collision {A B : Type*} [Fintype A] [Fintype B]
    (h : Fintype.card B < Fintype.card A) (f : A → B) : ¬ Injective f := fun hf =>
  absurd (Fintype.card_le_of_injective f hf) (not_le.mpr h)

/-- There are `2 ^ (2 ^ n)` Boolean functions on `n` bits. -/
