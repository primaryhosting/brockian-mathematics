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

theorem stability_of_second_kind
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (ρ : α → ℝ≥0∞)
    (hρ : AEMeasurable ρ μ)
    {N t : ℝ} (hN : 0 ≤ N) (ht : 0 ≤ t)
    (hmass : particleNumber μ ρ = ENNReal.ofReal N)
    (hkin : ltKineticFunctional μ ρ = ENNReal.ofReal t)
    {K_LT C_ES c_nuc M T V E : ℝ} (hK : 0 < K_LT) (hC : 0 ≤ C_ES)
    (hM : 0 ≤ M)
    (hLT : K_LT * t ≤ T)
    (hES : -(C_ES * (coulombFunctional μ ρ).toReal) - c_nuc * M ≤ V)
    (hE : E = T + V) :
    -(max (C_ES ^ 2 / (4 * K_LT)) c_nuc) * (N + M) ≤ E := by
  have h := lieb_thirring_stability ρ hρ hN ht hmass hkin (K_LT := K_LT) (C_ES := C_ES)
    (C_nuc := c_nuc * M) hK hC hLT hES hE
  set c := max (C_ES ^ 2 / (4 * K_LT)) c_nuc with hcdef
  have h1 : C_ES ^ 2 / (4 * K_LT) ≤ c := le_max_left _ _
  have h2 : c_nuc ≤ c := le_max_right _ _
  have hb1 : C_ES ^ 2 / (4 * K_LT) * N ≤ c * N := by nlinarith
  have hb2 : c_nuc * M ≤ c * M := by nlinarith
  nlinarith [h, hb1, hb2]

/-!
### Non-vacuity

The hypotheses of `lieb_thirring_stability` are satisfiable: a concrete density
on a one-point measure space, together with concrete energies, realises them.
-/

/-- A concrete instance showing the hypotheses of `lieb_thirring_stability` are
consistent (a unit density on a one-point space, with `N = t = ∫ ρ^(4/3) = 1`). -/
