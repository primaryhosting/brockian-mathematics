import Mathlib
namespace C6.Alg7


theorem inv_inv_group {G : Type*} [Group G] (a : G) : a⁻¹⁻¹ = a :=
  inv_inv a

