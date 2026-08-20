import Mathlib
namespace C5.Alg6

/-- The kernel of a group homomorphism is a normal subgroup. -/

theorem conj_preserves_order {G : Type*} [Group G] (g a : G) :
    orderOf (g * a * g⁻¹) = orderOf a := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  simpa [MulAut.conj] using this

end C5.Alg6

