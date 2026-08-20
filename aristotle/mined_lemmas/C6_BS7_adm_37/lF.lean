import Mathlib
namespace C6.BS7

noncomputable def lF (G : Finset ℕ) (p : ℕ) : ℝ := if p.Prime then (1-(nu G p:ℝ)/p)/((1-1/(p:ℝ))^G.card) else 1

/-- For `g ≠ 0` in `ZMod 37`, exactly `35` residues avoid both `0` and `-g`:
the excluded set `{0, -g}` has two elements, and `37 - 2 = 35`. -/
