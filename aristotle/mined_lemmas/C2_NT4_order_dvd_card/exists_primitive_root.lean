import Mathlib
namespace C2.NT4

/-- The order of a unit in `ZMod p` divides `p - 1`, the cardinality of `(ZMod p)ˣ`. -/

theorem exists_primitive_root (p : ℕ) [Fact p.Prime] : ∃ g : (ZMod p)ˣ, orderOf g = p - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  exact ⟨g, by rwa [Nat.card_eq_fintype_card, ZMod.card_units p] at hg⟩

/-- Fermat's little theorem, stated for units of `ZMod p`. -/
