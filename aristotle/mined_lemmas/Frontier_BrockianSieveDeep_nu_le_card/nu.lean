import Mathlib
namespace Frontier.BrockianSieveDeep

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

