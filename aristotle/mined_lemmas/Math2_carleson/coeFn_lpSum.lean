/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import line, so the
required header is reproduced here as a plain comment and again as a module
docstring immediately after the import.)
-/

import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

open MeasureTheory Filter Topology
open scoped ENNReal

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th symmetric partial sum of the Fourier series of `f` at the point `x`. -/

lemma coeFn_lpSum {α : Type*} [MeasurableSpace α] {mu : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {ι : Type*} (s : Finset ι) (F : ι → Lp ℂ p mu) :
    ⇑(∑ i ∈ s, F i) =ᵐ[mu] fun x => ∑ i ∈ s, F i x := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Lp.coeFn_zero ℂ p mu
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (F a) (∑ i ∈ s, F i), ih] with x h1 h2
      rw [h1, Finset.sum_insert ha, Pi.add_apply, h2]

/-- The symmetric partial sums of the Fourier series of an `L²` function converge to it
in the `L²` norm. -/
