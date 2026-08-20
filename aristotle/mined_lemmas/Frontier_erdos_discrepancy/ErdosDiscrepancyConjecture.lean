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

def ErdosDiscrepancyConjecture : Prop :=
  ∀ f : Nat → Int, IsPlusMinusOne f → HasUnboundedDiscrepancy f

/-- Key step: a `±1` sequence all of whose homogeneous partial sums have absolute value at
most `1` does not exist; the contradiction is already visible among `f 1, …, f 12`. -/
