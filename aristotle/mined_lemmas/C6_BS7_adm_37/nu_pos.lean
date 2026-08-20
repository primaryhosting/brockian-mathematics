import Mathlib
namespace C6.BS7

theorem nu_pos (G : Finset ℕ) (p : ℕ) (hG : G.Nonempty) : 0 < nu G p :=
  Finset.card_pos.mpr (hG.image _)
end C6.BS7

