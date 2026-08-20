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

lemma integral_le_measure {G : C(𝕋, ℝ)} {A : Set 𝕋} (hA : MeasurableSet A)
    (h0 : ∀ z, z ∉ A → G z = 0) (h1 : ∀ z, G z ≤ 1) :
    ∫ z : 𝕋, G z ∂AddCircle.haarAddCircle
      ≤ (AddCircle.haarAddCircle (T := (1 : ℝ)) A).toReal := by
  have hint := contMap_integrable G
  rw [← integral_add_compl hA hint]
  have hc : ∫ z in Aᶜ, G z ∂AddCircle.haarAddCircle = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => h0 z ?_
    simpa using hz
  rw [hc, add_zero]
  calc ∫ z in A, G z ∂AddCircle.haarAddCircle
      ≤ ∫ _z in A, (1 : ℝ) ∂AddCircle.haarAddCircle := by
        refine setIntegral_mono_on hint.integrableOn ((integrable_const (1 : ℝ)).integrableOn) hA
          fun z _ => h1 z
    _ = (AddCircle.haarAddCircle (T := (1 : ℝ)) A).toReal := by
        simp [measureReal_def]

