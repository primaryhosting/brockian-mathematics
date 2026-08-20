import Mathlib
namespace Frontier.BrockianSieveDeep

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

theorem nu_le_card (G : Finset ℕ) (p : ℕ) : nu G p ≤ G.card :=
  Finset.card_image_le
