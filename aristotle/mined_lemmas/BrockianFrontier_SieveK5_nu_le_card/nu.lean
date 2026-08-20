import Mathlib
namespace BrockianFrontier.SieveK5

/-- Residues covered by `G` mod `p`. -/

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

/-- Hardy–Littlewood local factor of a gap-set at a prime. -/
