import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/

theorem erdos_discrepancy_quantitative (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ d * n ≤ 12 ∧ 2 ≤ |apSum f d n| := by
  by_contra hcon
  push_neg at hcon
  refine no_discrepancy_one_sequence f hf (fun d n hd hn hdn => ?_)
  have := hcon d n hd hn hdn
  omega

/-- **Erdős discrepancy, base case.**  Every `±1` sequence has discrepancy at least `2`
along some homogeneous arithmetic progression: there are `d, n ≥ 1` with
`|f d + f 2d + ⋯ + f nd| ≥ 2`.  (This is the case `C = 1` of the full statement
`Frontier.ErdosDiscrepancy`.) -/
