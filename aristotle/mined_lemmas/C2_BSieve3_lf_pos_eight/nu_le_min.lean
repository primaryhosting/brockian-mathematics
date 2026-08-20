import Mathlib
namespace C2.BSieve3

theorem nu_le_min (G : Finset ℕ) (p : ℕ) (hp : 0 < p) : nu G p ≤ min G.card p := by
  refine le_min Finset.card_image_le ?_
  have hsub : G.image (· % p) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact Finset.mem_range.2 (Nat.mod_lt _ hp)
  simpa using Finset.card_le_card hsub

/-- For nonzero `g` in `ZMod 13`, exactly `11` residues avoid both `0` and `-g`. -/
