import Mathlib
namespace C5.BS6

noncomputable def lF (G : Finset ℕ) (p : ℕ) : ℝ := if p.Prime then (1-(nu G p:ℝ)/p)/((1-1/(p:ℝ))^G.card) else 1

/-- The 11-tuple `{0,2,6,8,12,18,20,26,30,32,36}` is admissible: for every prime `p`
it omits at least one residue class mod `p`. -/
