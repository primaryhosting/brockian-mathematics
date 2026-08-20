import Mathlib
namespace MS2.Algebra2

theorem orbit_stabilizer {G α : Type*} [Group G] [MulAction G α] [Fintype G] (a : α) [Fintype (MulAction.orbit G a)] [Fintype (MulAction.stabilizer G a)] :
    Fintype.card (MulAction.orbit G a) * Fintype.card (MulAction.stabilizer G a) = Fintype.card G :=
  MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a
