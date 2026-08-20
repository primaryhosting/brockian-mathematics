import Mathlib
namespace Frontier.AlgebraLogic

theorem cayley_embedding {G : Type*} [Group G] : ∃ f : G →* Equiv.Perm G, Function.Injective f :=
  ⟨MulAction.toPermHom G G, by
    intro a b hab
    have := congrArg (fun p : Equiv.Perm G => p 1) hab
    simpa [MulAction.toPermHom] using this⟩
end Frontier.AlgebraLogic

