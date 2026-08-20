import Mathlib
namespace Frontier.BrockianSieveDeep

theorem nu_le_card (G : Finset ℕ) (p : ℕ) : nu G p ≤ G.card :=
  Finset.card_image_le

