/-
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The substitution `x = eᵗ` induces the *Mellin logarithmic change of variables*

`(U f)(t) = e^{t/2} • f (eᵗ)`,  `(U⁻¹ h)(x) = x^{-1/2} • h (log x)`,

which is a unitary `L²(0, ∞) ≃ L²(ℝ)`.  This file proves:

* `Brockian.DilationGenerator.map_exp_withDensity_exp`: the pushforward of
  `e^t dt` under `exp` is Lebesgue measure on `(0, ∞)` (the underlying
  change-of-variables statement, from `map_withDensity_abs_det_fderiv_eq_addHaar`);
* `Brockian.DilationGenerator.measurePreserving_exp`: the same fact phrased as
  `MeasurePreserving`;
* `Brockian.DilationGenerator.lintegral_Ioi_eq_lintegral_exp`: the change of
  variables for `ℝ≥0∞`-valued integrands (no hypotheses on the integrand);
* `Brockian.DilationGenerator.mellin_log_unitary`: **the target** — the map
  `U` preserves the `L²` integral, for an arbitrary `f : ℝ → E`;
* `Brockian.DilationGenerator.eLpNorm_mellinLog`: the `L²` seminorm identity
  `eLpNorm (U f) 2 volume = eLpNorm f 2 (volume.restrict (Ioi 0))` in `ℝ≥0∞`,
  again with no hypotheses on `f`;
* `Brockian.DilationGenerator.mellinLogSymm_mellinLog` and
  `Brockian.DilationGenerator.mellinLog_mellinLogSymm`: `U` and `U⁻¹` are
  mutually inverse (pointwise, on `(0, ∞)` resp. on `ℝ`);
* `Brockian.DilationGenerator.mellinLogUnitary`: the Lp upgrade — `U` as a
  surjective linear isometry (unitary)
  `L²((0,∞), dx) ≃ₗᵢ[𝕜] L²(ℝ, dt)`, with `U⁻¹` given by `mellinLogLpSymm`.

The first line of the file repeats the required header as a plain (non-doc)
comment, since Lean does not allow a module docstring before `import`.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal NNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.DilationGenerator

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E]

/-- The logarithmic substitution `x = eᵗ` applied to a function on `(0, ∞)`:
`(U f)(t) = e^{t/2} • f (eᵗ)`. -/

noncomputable def expWeightedMeasure : Measure ℝ :=
  (volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp t)

/-- The pushforward of the measure `eᵗ dt` under `exp` is Lebesgue measure on `(0, ∞)`. -/
