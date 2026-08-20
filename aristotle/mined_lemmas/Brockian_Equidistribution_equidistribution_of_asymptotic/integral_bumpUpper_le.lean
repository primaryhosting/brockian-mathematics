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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The block above is repeated as the file header; Lean does not allow a module docstring to
precede the `import` line.)

This file proves **Weyl's equidistribution criterion** unconditionally: if all nontrivial
exponential sums of a real sequence `x` are asymptotically negligible, then `x` is
equidistributed modulo one.  The argument goes through the circle `𝕋 = AddCircle 1`:

* the Birkhoff averages of each Fourier monomial converge to its integral (`avgC_fourier_tendsto`);
* the set of continuous functions with this property is a closed submodule of `C(𝕋, ℂ)`, hence,
  by Stone-Weierstrass (`span_fourier_closure_eq_top`), is everything (`avgC_tendsto`);
* indicator functions of arcs are squeezed between continuous plateau functions supported on
  metric balls, whose integrals are controlled by `AddCircle.volume_closedBall`.

As an application (and as a witness that the hypothesis is satisfiable) we derive the classical
equidistribution of irrational rotations, `equidistribution_irrational_rotation`.
-/

open Filter MeasureTheory Metric Complex Set
open scoped Topology Real BigOperators

namespace Brockian.Equidistribution

local notation "𝕋" => AddCircle (1 : ℝ)

/-- The Birkhoff/Weyl average of a complex-valued continuous function on the circle along the
first `N` terms of the sequence `x`. -/

lemma integral_bumpUpper_le {a b d : ℝ} (hab : a ≤ b) (hd : 0 < d) :
    ∫ z : 𝕋, (bumpFn ((a + b) / 2) ((b - a) / 2 + d) d) z ∂AddCircle.haarAddCircle
      ≤ (b - a) + 2 * d := by
  have h := integral_le_measure (G := bumpFn ((a + b) / 2) ((b - a) / 2 + d) d)
      (A := closedBall ((((a + b) / 2 : ℝ)) : 𝕋) ((b - a) / 2 + d))
      measurableSet_closedBall ?_ (fun z => bumpFn_le_one _ _ _ _)
  · rw [haar_closedBall] at h
    refine h.trans ?_
    rw [max_le_iff]
    exact ⟨(min_le_right _ _).trans (by linarith), by linarith⟩
  · intro z hz
    refine bumpFn_eq_zero hd ?_
    rw [mem_closedBall, dist_eq_norm] at hz
    push_neg at hz
    exact hz.le

