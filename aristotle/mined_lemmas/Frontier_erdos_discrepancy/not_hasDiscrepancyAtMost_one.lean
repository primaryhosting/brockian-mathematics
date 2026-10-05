/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- A `±1` sequence, indexed by the positive naturals (the value at `0` is irrelevant). -/

theorem not_hasDiscrepancyAtMost_one (hf : IsPlusMinusOne f) :
    ¬ HasDiscrepancyAtMost f 1 := by
  intro hb
  have pair := fun {d : ℕ} (hd : 1 ≤ d) (j : ℕ) => pair_eq_zero hf hb hd j
  -- f 2 = - f 1
  have h2 : f 1 + f 2 = 0 := by simpa using pair (d := 1) (by norm_num) 0
  -- f 4 = - f 2
  have h4 : f 2 + f 4 = 0 := by simpa using pair (d := 2) (by norm_num) 0
  -- f 3 + f 4 = 0
  have h3 : f 3 + f 4 = 0 := by simpa using pair (d := 1) (by norm_num) 1
  -- f 6 = - f 3
  have h6 : f 3 + f 6 = 0 := by simpa using pair (d := 3) (by norm_num) 0
  -- f 5 + f 6 = 0
  have h5 : f 5 + f 6 = 0 := by simpa using pair (d := 1) (by norm_num) 2
  -- f 10 = - f 5
  have h10 : f 5 + f 10 = 0 := by simpa using pair (d := 5) (by norm_num) 0
  -- f 9 + f 10 = 0
  have h9 : f 9 + f 10 = 0 := by simpa using pair (d := 1) (by norm_num) 4
  -- f 12 = - f 6
  have h12 : f 6 + f 12 = 0 := by simpa using pair (d := 6) (by norm_num) 0
  -- f 9 + f 12 = 0
  have h912 : f 9 + f 12 = 0 := by simpa using pair (d := 3) (by norm_num) 1
  have hone : f 1 = 1 ∨ f 1 = -1 := hf 1 le_rfl
  omega

end BaseCase

/-- **Erdős discrepancy problem, base case (`C = 1`).**  For every `±1` sequence `f` there are
a common difference `d ≥ 1` and a length `n` with `|f d + f (2d) + ⋯ + f (nd)| ≥ 2`.
(The full theorem of Tao, stated here as `Frontier.ErdosDiscrepancyConjecture`, asserts that
these sums are unbounded; this is its first nontrivial case.) -/
