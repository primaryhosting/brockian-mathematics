import Mathlib
namespace C5.Alg6

/-- The kernel of a group homomorphism is a normal subgroup. -/

theorem index_mul_card {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    H.index * Fintype.card H = Fintype.card G := by
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Subgroup.index_mul_card]

/-- Conjugation preserves the order of an element. -/
