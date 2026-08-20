import Mathlib
namespace BrockianFrontier.SingularSeries

/-- Number of residues covered by `G` modulo `p`. -/

noncomputable def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - (nu G p : ℝ) / p) / ((1 - 1 / (p : ℝ)) ^ G.card) else 1

/-- Admissibility (`nu G p < p` at every prime `p`) forces the local factor to be positive. -/
