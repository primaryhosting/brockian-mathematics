import Mathlib
namespace C4.BS5


def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

