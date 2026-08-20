import Mathlib
namespace C4.BS5


noncomputable def lF (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1-(nu G p:ℝ)/p)/((1-1/(p:ℝ))^G.card) else 1

/-- The set `{0,2,6,8,12,18,20,26,30,32}` is admissible: for every prime `p` it omits a
residue class mod `p`, hence its local factor `lF` is positive. -/
