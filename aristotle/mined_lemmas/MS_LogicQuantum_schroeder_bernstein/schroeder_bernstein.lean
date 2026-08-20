import Mathlib
open Matrix
namespace MS.LogicQuantum


theorem schroeder_bernstein {α β : Type*} (f : α → β) (g : β → α)
    (hf : Function.Injective f) (hg : Function.Injective g) : Nonempty (α ≃ β) := by
  obtain ⟨h, hh⟩ := Function.Embedding.schroeder_bernstein hf hg
  exact ⟨Equiv.ofBijective h hh⟩

