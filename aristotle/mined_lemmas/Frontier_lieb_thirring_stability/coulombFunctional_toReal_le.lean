/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module
-- docstring only because Lean 4 requires `import` to precede any docstring;
-- the identical module docstring is reproduced immediately after the imports.)

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

/-!
## Overview

The Lieb–Thirring route to the *stability of matter* combines three ingredients:

1. **The Lieb–Thirring kinetic energy inequality.**  For a normalized fermionic
   wave function `Ψ` of `N` particles with one-particle density `ρ`, the kinetic
   energy obeys `T ≥ K_LT * ∫ ρ^(5/3)`.

2. **An electrostatic (Baxter / Lieb–Yau type) inequality.**  The full Coulomb
   interaction of electrons and nuclei is bounded below by a purely local term,
   `V ≥ - C_ES * ∫ ρ^(4/3) - C_nuc`, where `C_nuc` collects the nucleus-dependent
   contribution (proportional to the number of nuclei).

3. **A functional-analytic interpolation step**, which turns the competition
   between the two local terms into a bound that is *linear in the particle
   number* `N = ∫ ρ`.

Step 3 is the mathematical heart of the reduction, and it is what is proved here
from scratch: by Cauchy–Schwarz (the `p = q = 2` case of Hölder's inequality)

  `∫ ρ^(4/3) = ∫ ρ^(1/2) · ρ^(5/6) ≤ (∫ ρ)^(1/2) · (∫ ρ^(5/3))^(1/2)`,

so that with `t = ∫ ρ^(5/3)` and `N = ∫ ρ`,

  `T + V ≥ K_LT * t - C_ES * √N * √t - C_nuc ≥ - (C_ES^2 / (4 K_LT)) * N - C_nuc`

by the arithmetic–geometric mean inequality.  The conclusion is exactly
*stability of the second kind*: the energy per particle is bounded below by a
constant that does not depend on `N`.

Everything below is stated for an arbitrary measure space, so that it applies
verbatim to `ρ : ℝ³ → ℝ≥0∞` with Lebesgue measure.  Densities are taken to be
`ℝ≥0∞`-valued so that all the integrals are unconditionally defined; the two
physical input inequalities (1) and (2) enter as hypotheses, and the deduction of
stability from them is fully verified.
-/

namespace Frontier

open MeasureTheory ENNReal

section Densities

variable {α : Type*} [MeasurableSpace α]

/-- The total mass (particle number) `∫ ρ` of a one-particle density `ρ`. -/

theorem coulombFunctional_toReal_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (ρ : α → ℝ≥0∞)
    (hρ : AEMeasurable ρ μ) {N t : ℝ} (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hmass : particleNumber μ ρ = ENNReal.ofReal N)
    (hkin : ltKineticFunctional μ ρ = ENNReal.ofReal t) :
    (coulombFunctional μ ρ).toReal ≤ Real.sqrt N * Real.sqrt t := by
  have hle := coulombFunctional_le ρ hρ
  rw [hmass, hkin] at hle
  have hfin : (ENNReal.ofReal N) ^ (1 / 2 : ℝ) * (ENNReal.ofReal t) ^ (1 / 2 : ℝ) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ?_ <;>
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by simp)
  have h1 : (coulombFunctional μ ρ).toReal ≤
      ((ENNReal.ofReal N) ^ (1 / 2 : ℝ) * (ENNReal.ofReal t) ^ (1 / 2 : ℝ)).toReal :=
    ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin hle) hfin |>.mpr hle
  refine h1.trans_eq ?_
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hN, ENNReal.toReal_ofReal ht, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-!
### The arithmetic–geometric mean step
-/

/-- **The AM–GM step.**  For `K > 0` and `N, t ≥ 0` (any real `C`),
`K t - C √N √t ≥ - C^2 N / (4 K)`.  This is the completion of the square
`K t - C √N √t + C^2 N / (4K) = (2 K √t - C √N)^2 / (4K)`. -/
