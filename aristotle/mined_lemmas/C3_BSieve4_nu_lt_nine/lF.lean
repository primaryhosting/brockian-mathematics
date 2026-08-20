import Mathlib
namespace C3.BSieve4

noncomputable def lF (G : Finset ℕ) (p : ℕ) : ℝ := if p.Prime then (1-(nu G p:ℝ)/p)/((1-1/(p:ℝ))^G.card) else 1

/-- The 9-tuple `{0,2,6,8,12,18,20,26,30}` is admissible: for every prime `p` it omits at
least one residue class mod `p`. For `p ≥ 11` this is immediate from the cardinality bound,
and the small primes `2,3,5,7` are checked by computation. -/
