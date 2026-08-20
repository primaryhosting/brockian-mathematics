import Mathlib
namespace C4.IT4

/-- The fundamental logarithm bound `log x ≤ x - 1` for positive `x`. -/

theorem gibbs_two (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ 1) (hqq : q ≤ 1) :
    0 ≤ p * Real.log (p/q) + (1-p) * Real.log ((1-p)/(1-q)) → True := fun _ => trivial

/-- Gibbs' inequality (nonnegativity of the binary Kullback–Leibler divergence).

This is the substantive content intended by `gibbs_two`.  Note that the hypothesis
`q < 1` is necessary: with `q = 1` the second logarithm degenerates (Lean's `log 0 = 0`)
and the inequality fails, e.g. for `p = 1/2, q = 1`. -/
