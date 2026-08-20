import Mathlib
namespace Frontier.AlgebraLogic

theorem lagrange {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H
