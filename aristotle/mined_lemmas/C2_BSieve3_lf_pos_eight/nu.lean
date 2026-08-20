import Mathlib
namespace C2.BSieve3

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
