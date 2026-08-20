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

lemma le_integral_bumpLower {a b d : ℝ} (hb1 : b - a ≤ 1) (hd : 0 < d) :
    (b - a) - 2 * d
      ≤ ∫ z : 𝕋, (bumpFn ((a + b) / 2) ((b - a) / 2) d) z ∂AddCircle.haarAddCircle := by
  have h := measure_le_integral (G := bumpFn ((a + b) / 2) ((b - a) / 2) d)
      (A := closedBall ((((a + b) / 2 : ℝ)) : 𝕋) ((b - a) / 2 - d))
      measurableSet_closedBall ?_ (fun z => bumpFn_nonneg _ _ _ _)
  · rw [haar_closedBall] at h
    refine le_trans ?_ h
    have hmin : min 1 (2 * ((b - a) / 2 - d)) = 2 * ((b - a) / 2 - d) :=
      min_eq_right (by linarith)
    calc (b - a) - 2 * d = min 1 (2 * ((b - a) / 2 - d)) := by rw [hmin]; ring
      _ ≤ max (min 1 (2 * ((b - a) / 2 - d))) 0 := le_max_left _ _
  · intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    exact le_of_eq (bumpFn_eq_one hd hz).symm

/-! ### Main theorem -/

/-- **Weyl's equidistribution criterion.**  If all nontrivial exponential sums of a real
sequence `x` are asymptotically negligible, then `x` is equidistributed modulo one: for every
subinterval `[a, b) ⊆ [0, 1]`, the proportion of the first `N` terms whose fractional part lies
in `[a, b)` converges to the length `b - a`. -/
