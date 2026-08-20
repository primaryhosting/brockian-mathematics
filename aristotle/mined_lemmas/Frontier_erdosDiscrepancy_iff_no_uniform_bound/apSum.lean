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

def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- **The Erdős discrepancy problem** (a theorem of Tao, 2015), as a formal statement:
every `±1` sequence has unbounded discrepancy along homogeneous arithmetic progressions,
i.e. for every bound `C` there are `d, n ≥ 1` with `|f d + f 2d + ⋯ + f nd| > C`. -/
