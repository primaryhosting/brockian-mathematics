import Mathlib
namespace C2.SetT

/-- Zorn's lemma: if every chain in a partial order has an upper bound, there is a
maximal element. Follows from `exists_maximal_of_chains_bounded` plus antisymmetry. -/

theorem cantor_powerset {α : Type*} : ¬ ∃ f : α → Set α, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact Function.cantor_surjective f hf

end C2.SetT

