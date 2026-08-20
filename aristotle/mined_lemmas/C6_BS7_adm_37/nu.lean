import Mathlib
namespace C6.BS7

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
