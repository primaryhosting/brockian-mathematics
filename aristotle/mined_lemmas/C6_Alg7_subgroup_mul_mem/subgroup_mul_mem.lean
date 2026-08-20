import Mathlib
namespace C6.Alg7


theorem subgroup_mul_mem {G : Type*} [Group G] (H : Subgroup G) (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a*b ∈ H :=
  H.mul_mem ha hb

