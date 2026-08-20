import Mathlib
namespace BrockianFrontier.SieveK5

/-- Residues covered by `G` mod `p`. -/

noncomputable def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - (nu G p : ℝ) / p) / ((1 - 1 / (p : ℝ)) ^ G.card) else 1

/-- The number of covered residues never exceeds the size of the gap-set. -/
