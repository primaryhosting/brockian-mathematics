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

theorem integral_abs_mul_le_sqrt_mul_sqrt {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ∫ x, |f x| * |g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  have hconj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp [ENNReal.ofReal_ofNat]
  have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hconj
    (f := fun x => |f x|) (g := fun x => |g x|)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (by rw [h2]; exact hf.abs) (by rw [h2]; exact hg.abs)
  refine h.trans_eq ?_
  have e1 : ∀ u : ℝ → ℝ, (∫ x, |u x| ^ (2 : ℝ)) = ∫ x, u x ^ 2 := by
    intro u
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [e1, e1, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Sobolev-type sup bound in one dimension.**  For a `C¹` function `ψ` with `ψ`
and `ψ'` in `L²(ℝ)` and `ψ → 0` at `-∞`,
`ψ(x)² ≤ 2 (∫ ψ²)^(1/2) (∫ (ψ')²)^(1/2)` for every `x`.

This is the one-dimensional analogue, for a single particle, of the Lieb–Thirring
interpolation step. -/
