import Mathlib
namespace MS.Algebra


theorem cayley_embedding {G : Type*} [Group G] :
    ∃ f : G →* Equiv.Perm G, Function.Injective f :=
  ⟨MulAction.toPermHom G G, fun a b h => by
    simpa using congrArg (fun e : Equiv.Perm G => e 1) h⟩

end MS.Algebra

