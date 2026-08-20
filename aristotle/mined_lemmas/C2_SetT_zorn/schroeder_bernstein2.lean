import Mathlib
namespace C2.SetT

/-- Zorn's lemma: if every chain in a partial order has an upper bound, there is a
maximal element. Follows from `exists_maximal_of_chains_bounded` plus antisymmetry. -/

theorem schroeder_bernstein2 {α β : Type*} (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (α ≃ β) :=
  Function.Embedding.antisymm ⟨f, hf⟩ ⟨g, hg⟩

/-- Cantor's theorem: no map `α → Set α` is surjective. -/
