import Mathlib
namespace BrockianFrontier.SingularSeries

/-- Number of residues covered by `G` modulo `p`. -/

def nu (G : Finset ℕ) (p : ℕ) : ℕ := (G.image (· % p)).card

/-- The Hardy–Littlewood local factor of an admissible set `G` at `p`. -/
