import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma geom_nat (c p : ℕ) : (∑ i ∈ Finset.range p, (c + 1) ^ i) * c + 1 = (c + 1) ^ p := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; nlinarith [ih]

/-- The "alternating" geometric sum identity over `ℕ`: for odd exponents `2 * m + 1`,
`y + 1` divides `y ^ (2 * m + 1) + 1`, with an explicit cofactor which is visibly odd
when `y = w + 1` and `w` is even. -/
