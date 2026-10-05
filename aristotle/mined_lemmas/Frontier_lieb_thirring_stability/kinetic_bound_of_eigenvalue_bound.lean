/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## Overview

The Lieb–Thirring inequality (in three dimensions, for the exponent `γ = 1`) comes in two
equivalent guises:

* the **eigenvalue form**: for a one-body potential `V ≥ 0`, the sum of the negative
  eigenvalues of the Schrödinger operator `-Δ - V` is bounded below by
  `-L * ∫ V ^ (5/2)`, i.e. for any system of `N` orthonormal states with one-particle
  density `ρ` and kinetic energy `T`, one has `T - ∫ ρ * V ≥ -L * ∫ V ^ (5/2)`;

* the **kinetic-energy form**: `T ≥ K * ∫ ρ ^ (5/3)` — a Thomas–Fermi lower bound on the
  kinetic energy in terms of the one-particle density alone.

The passage between the two forms is a Legendre-duality argument, and the kinetic-energy
form is exactly the ingredient that yields *stability of matter*: the total energy is
bounded below by a quantity that does not depend on the number of particles.

This file formalizes that duality completely and rigorously, on an arbitrary measure space:

* `Frontier.young_five_thirds` — the pointwise Legendre/Young inequality
  `x * y ≤ K * x ^ (5/3) + ltDualConst K * y ^ (5/2)` with the optimal constant
  `ltDualConst K = (2/5) * (3/(5*K)) ^ (3/2)`;
* `Frontier.kinetic_bound_of_eigenvalue_bound` — the reduction from the eigenvalue form
  (with constant `L`) to the kinetic-energy form, with the explicit constant
  `ltKineticConst L = (3/5) * (2/(5*L)) ^ (2/3)`;
* `Frontier.lieb_thirring_stability` — the main target: the kinetic-energy form implies a
  lower bound on the total energy `T - ∫ ρ * V` which is uniform in the state (in
  particular uniform in the particle number), depending only on the external potential
  through `∫ V ^ (5/2)`.

Everything is stated for the *density* `ρ` and *kinetic energy* `T` of a state, which is
the level at which the Lieb–Thirring argument actually operates; no analytic facts about
Schrödinger operators are assumed beyond the two hypotheses that are being related.
-/

namespace Frontier

open MeasureTheory

/-- The optimal constant in the Legendre duality between the exponents `5/3` and `5/2`:
if the kinetic-energy (Thomas–Fermi) constant is `K`, the dual eigenvalue-sum constant is
`ltDualConst K = (2/5) * (3/(5*K)) ^ (3/2)`. -/

theorem kinetic_bound_of_eigenvalue_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {L T : ℝ} (hL : 0 < L) {ρ : α → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable (fun x => ρ x ^ (5/3 : ℝ)) μ)
    (hLT : ∀ V : α → ℝ, Measurable V → (∀ x, 0 ≤ V x) →
      Integrable (fun x => V x ^ (5/2 : ℝ)) μ →
      -(L * ∫ x, V x ^ (5/2 : ℝ) ∂μ) ≤ T - ∫ x, ρ x * V x ∂μ) :
    ltKineticConst L * ∫ x, ρ x ^ (5/3 : ℝ) ∂μ ≤ T := by
  set b : ℝ := 2 / (5 * L) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  set c : ℝ := b ^ (2/3 : ℝ) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos hb0 _
  set V : α → ℝ := fun x => c * ρ x ^ (2/3 : ℝ) with hV
  have hVm : Measurable V := (hρm.pow_const (2/3 : ℝ)).const_mul c
  have hV0 : ∀ x, 0 ≤ V x := fun x =>
    mul_nonneg hc0.le (Real.rpow_nonneg (hρ0 x) _)
  -- `V ^ (5/2) = c ^ (5/2) * ρ ^ (5/3)`
  have hVpow : ∀ x, V x ^ (5/2 : ℝ) = c ^ (5/2 : ℝ) * ρ x ^ (5/3 : ℝ) := by
    intro x
    rw [hV]
    simp only
    rw [Real.mul_rpow hc0.le (Real.rpow_nonneg (hρ0 x) _), ← Real.rpow_mul (hρ0 x)]
    norm_num
  -- `ρ * V = c * ρ ^ (5/3)`
  have hprod : ∀ x, ρ x * V x = c * ρ x ^ (5/3 : ℝ) := by
    intro x
    rw [hV]
    simp only
    rw [← mul_assoc, mul_comm (ρ x) c, mul_assoc]
    congr 1
    nth_rewrite 1 [← Real.rpow_one (ρ x)]
    rw [← Real.rpow_add' (hρ0 x) (by norm_num)]
    norm_num
  have hVi : Integrable (fun x => V x ^ (5/2 : ℝ)) μ := by
    have : (fun x => V x ^ (5/2 : ℝ)) = fun x => c ^ (5/2 : ℝ) * ρ x ^ (5/3 : ℝ) :=
      funext hVpow
    rw [this]
    exact hρi.const_mul _
  have key := hLT V hVm hV0 hVi
  set A : ℝ := ∫ x, ρ x ^ (5/3 : ℝ) ∂μ with hA
  have h1 : ∫ x, V x ^ (5/2 : ℝ) ∂μ = c ^ (5/2 : ℝ) * A := by
    rw [hA, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hVpow)
  have h2 : ∫ x, ρ x * V x ∂μ = c * A := by
    rw [hA, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hprod)
  rw [h1, h2] at key
  -- arithmetic: `c - L * c ^ (5/2) = (3/5) * c`
  have hc52 : c ^ (5/2 : ℝ) = c * b := by
    rw [hc, ← Real.rpow_mul hb0.le,
      show ((2:ℝ)/3) * (5/2) = 2/3 + 1 by norm_num, Real.rpow_add hb0, Real.rpow_one]
  have hLb : L * b = 2/5 := by
    rw [hb]; field_simp
  have hconst : ltKineticConst L = (3/5) * c := by rw [ltKineticConst, ← hb, ← hc]
  rw [hconst]
  have hkey2 : L * (c ^ (5/2 : ℝ) * A) = (2/5) * (c * A) := by
    rw [hc52]; linear_combination (c * A) * hLb
  linarith [key, hkey2]

/-- The two constants are Legendre-dual to one another: the dual of the kinetic-energy
constant produced from an eigenvalue-sum constant `L` is `L` itself.  This shows that the
reduction `kinetic_bound_of_eigenvalue_bound` followed by `lieb_thirring_stability`
returns exactly the bound one started from, i.e. the duality is lossless. -/
