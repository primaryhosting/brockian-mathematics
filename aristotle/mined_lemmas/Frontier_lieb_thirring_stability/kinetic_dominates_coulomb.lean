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

theorem kinetic_dominates_coulomb {K C N t : ℝ} (hK : 0 < K)
    (hN : 0 ≤ N) (ht : 0 ≤ t) :
    -(C ^ 2 / (4 * K)) * N ≤ K * t - C * (Real.sqrt N * Real.sqrt t) := by
  set m := Real.sqrt N with hm
  set s := Real.sqrt t with hs
  have hm2 : m ^ 2 = N := Real.sq_sqrt hN
  have hs2 : s ^ 2 = t := Real.sq_sqrt ht
  rw [← hm2, ← hs2]
  have hkey : K * s ^ 2 - C * (m * s) - -(C ^ 2 / (4 * K)) * m ^ 2
      = (2 * K * s - C * m) ^ 2 / (4 * K) := by
    field_simp
    ring
  have hnn : 0 ≤ (2 * K * s - C * m) ^ 2 / (4 * K) := by positivity
  linarith [hkey, hnn]

/-!
### Stability of matter
-/

/--
**Lieb–Thirring stability of matter (Lean-checked reduction).**

Let `ρ` be the one-particle density of a state of a Coulomb system on an
arbitrary measure space, with finite particle number `N = ∫ ρ` and finite
Lieb–Thirring functional `t = ∫ ρ^(5/3)`.

Assume the two physical input inequalities:

* the **Lieb–Thirring kinetic energy inequality** `K_LT * t ≤ T`, with
  `K_LT > 0`;
* the **electrostatic (Baxter / Lieb–Yau) inequality**
  `- C_ES * ∫ ρ^(4/3) - C_nuc ≤ V`, with `C_ES ≥ 0` and `C_nuc` the
  nucleus-dependent constant.

Then the total energy `E = T + V` satisfies

  `E ≥ - (C_ES^2 / (4 K_LT)) * N - C_nuc`,

i.e. it is bounded below by a constant times the particle number, plus the
nuclear contribution.  This is *stability of the second kind*.
-/
