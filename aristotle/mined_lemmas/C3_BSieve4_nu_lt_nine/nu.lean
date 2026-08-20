import Mathlib
namespace C3.BSieve4

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
