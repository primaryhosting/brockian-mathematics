import Mathlib
namespace Frontier.BrockianSieveDeep

theorem nu_le_prime (G : Finset ℕ) (p : ℕ) (hp : 0 < p) : nu G p ≤ p := by
  have hsub : G.image (· % p) ⊆ Finset.range p := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  simpa [nu] using (Finset.card_le_card hsub).trans_eq (Finset.card_range p)

