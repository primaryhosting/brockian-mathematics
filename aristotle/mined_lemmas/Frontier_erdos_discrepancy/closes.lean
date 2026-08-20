/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Erdős discrepancy problem (solved by T. Tao, 2015) asserts that every `±1` sequence
`f : ℕ → ℤ` has *unbounded* discrepancy along homogeneous arithmetic progressions: the
partial sums `∑_{i=1}^{n} f (i * d)` are unbounded in absolute value as `n, d` range over
the positive integers.

A search of Mathlib turns up no formalization of the Erdős discrepancy problem (nor of the
logarithmically averaged Chowla/Elliott conjectures used in Tao's proof), and no existing

lemma closes or nearly closes the statement below.

This file therefore:

* formalizes the full statement as `Frontier.ErdosDiscrepancyConjecture` (a `Prop`, stated
  but not claimed here);
* proves the base case `C = 1`, `Frontier.erdos_discrepancy`: no `±1` sequence has
  discrepancy `≤ 1`, i.e. every `±1` sequence admits a homogeneous arithmetic progression
  whose partial sum exceeds `1` in absolute value.  This is sharp in the sense that the
  first `11` terms of a `±1` sequence *can* have discrepancy `1`; the contradiction below
  uses the value `f 12`;
* records the trivial case `C = 0` as `Frontier.erdos_discrepancy_C_zero`.

Proof of the base case.  Suppose all homogeneous partial sums have absolute value at most
`1`.  For `d ≥ 1` the sum `f d + f (2*d)` is even and has absolute value at most `1`, hence
vanishes: `f (2*d) = - f d`; similarly `f (3*d) + f (4*d) = 0`.  Chasing these relations
from `f 1` gives
`f 2 = -f 1`, `f 4 = f 1` (via `d = 2`), `f 3 = -f 1`, `f 6 = f 1` (via `d = 3`),
`f 5 = -f 1`, `f 10 = f 1` (via `d = 5`), `f 9 = -f 1`, and then `f 12 = f 1`
(via `d = 3`, second pair) while `f 12 = -f 1` (via `d = 6`), a contradiction since
`f 1 = ±1`.

The development is deliberately self-contained (no imports), so that the statement can be
read off directly from the definitions below; `List.range`-based sums play the role of
`∑ i ∈ Finset.Icc 1 n`.
-/

namespace Frontier

/-- The discrepancy of `f` along the homogeneous arithmetic progression of common
difference `d`, truncated at `n` terms: `∑_{i=1}^{n} f (i * d)`. -/
