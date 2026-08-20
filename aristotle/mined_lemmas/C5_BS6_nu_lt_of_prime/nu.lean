import Mathlib
namespace C5.BS6

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card
