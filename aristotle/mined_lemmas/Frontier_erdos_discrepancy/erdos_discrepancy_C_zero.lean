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

theorem erdos_discrepancy_C_zero (f : Nat → Int) (hf : IsPlusMinusOne f) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ 0 < (apSum f d n).natAbs := by
  refine ⟨1, 1, Nat.le_refl _, Nat.le_refl _, ?_⟩
  have happ : apSum f 1 1 = f 1 + 0 := rfl
  have h := hf 1 (Nat.le_refl _)
  rw [happ]
  omega

end Frontier

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import RequestProject.ErdosDiscrepancy
import Mathlib

/-!
# Erdos Discrepancy — Mathlib restatement

Companion to `RequestProject/ErdosDiscrepancy.lean`, where the target theorem
`Frontier.erdos_discrepancy` is proved in a self-contained (import-free) form.

Here we identify the `List.range`-based partial sum `Frontier.apSum` with the usual
Mathlib sum `∑ i ∈ Finset.Icc 1 n, f (i * d)` and restate the results in that language.
-/

namespace Frontier

/-- `apSum f d n` is the sum `∑_{i=1}^{n} f (i * d)`. -/
