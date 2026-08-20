/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` all of whose values on positive integers
are `1` or `-1`. -/

def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- **The Erdős discrepancy problem** (theorem of Tao, 2016), as a `Prop`:
every `±1`-sequence has unbounded discrepancy along homogeneous arithmetic
progressions. -/
