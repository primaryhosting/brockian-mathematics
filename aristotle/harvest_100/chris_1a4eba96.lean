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
noncomputable def ltDualConst (K : ℝ) : ℝ := (2/5) * (3/(5*K)) ^ (3/2 : ℝ)

/-- The kinetic-energy (Thomas–Fermi) constant dual to an eigenvalue-sum constant `L`:
`ltKineticConst L = (3/5) * (2/(5*L)) ^ (2/3)`. -/
noncomputable def ltKineticConst (L : ℝ) : ℝ := (3/5) * (2/(5*L)) ^ (2/3 : ℝ)

/-- **Pointwise Legendre (Young) inequality for the Lieb–Thirring exponents.**
For nonnegative `x, y` and any `K > 0`,
`x * y ≤ K * x ^ (5/3) + ltDualConst K * y ^ (5/2)`.
The constant `ltDualConst K = (2/5) * (3/(5*K)) ^ (3/2)` is optimal: equality holds at
`y = (5*K/3) * x ^ (2/3)`. -/
theorem young_five_thirds {K x y : ℝ} (hK : 0 < K) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ K * x ^ (5/3 : ℝ) + ltDualConst K * y ^ (5/2 : ℝ) := by
  have hpq : (5/3 : ℝ).HolderConjugate (5/2) := by
    rw [Real.holderConjugate_iff]; norm_num
  set s : ℝ := (5 * K / 3) ^ (3/5 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos (by positivity) _
  have key := Real.young_inequality (s * x) (y / s) hpq
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at key
  have h1 : (s * x) * (y / s) = x * y := by field_simp
  rw [h1] at key
  have hsx : (s * x) ^ (5/3 : ℝ) = s ^ (5/3 : ℝ) * x ^ (5/3 : ℝ) := Real.mul_rpow hs0.le hx
  have hs53 : s ^ (5/3 : ℝ) = 5 * K / 3 := by
    rw [hs, ← Real.rpow_mul (by positivity)]; norm_num
  have hys : (y / s) ^ (5/2 : ℝ) = y ^ (5/2 : ℝ) / s ^ (5/2 : ℝ) := Real.div_rpow hy hs0.le _
  have hs52 : s ^ (5/2 : ℝ) = (5 * K / 3) ^ (3/2 : ℝ) := by
    rw [hs, ← Real.rpow_mul (by positivity)]; norm_num
  rw [hsx, hs53, hys, hs52] at key
  refine key.trans_eq ?_
  have h3 : (3 / (5 * K)) ^ (3/2 : ℝ) = ((5 * K / 3) ^ (3/2 : ℝ))⁻¹ := by
    rw [← Real.inv_rpow (by positivity)]
    congr 1
    field_simp
  have hpos : (0 : ℝ) < (5 * K / 3) ^ (3/2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  rw [ltDualConst, h3]
  field_simp

/-- **Main target: Lieb–Thirring ⇒ stability.**

If a state with one-particle density `ρ ≥ 0` and kinetic energy `T` satisfies the
Lieb–Thirring kinetic-energy bound `K * ∫ ρ ^ (5/3) ≤ T`, then in an arbitrary attractive
external potential `-V` (with `V ≥ 0` and `V ^ (5/2)` integrable) the total energy
`T - ∫ ρ * V` is bounded below by `-ltDualConst K * ∫ V ^ (5/2)`.

The lower bound depends only on the external potential — not on the state, and in
particular not on the number of particles.  This is exactly the mechanism by which the
Lieb–Thirring inequality gives stability of matter. -/
theorem lieb_thirring_stability {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K T : ℝ} (hK : 0 < K) {ρ V : α → ℝ}
    (hρm : AEStronglyMeasurable ρ μ) (hVm : AEStronglyMeasurable V μ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hV0 : ∀ x, 0 ≤ V x)
    (hρi : Integrable (fun x => ρ x ^ (5/3 : ℝ)) μ)
    (hVi : Integrable (fun x => V x ^ (5/2 : ℝ)) μ)
    (hkin : K * ∫ x, ρ x ^ (5/3 : ℝ) ∂μ ≤ T) :
    -(ltDualConst K * ∫ x, V x ^ (5/2 : ℝ) ∂μ) ≤ T - ∫ x, ρ x * V x ∂μ := by
  set L : ℝ := ltDualConst K with hL
  have hLpos : 0 < L := by
    rw [hL, ltDualConst]
    have : (0 : ℝ) < (3 / (5 * K)) ^ (3/2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    positivity
  -- the dominating function
  set g : α → ℝ := fun x => K * ρ x ^ (5/3 : ℝ) + L * V x ^ (5/2 : ℝ) with hg
  have hgi : Integrable g μ := (hρi.const_mul K).add (hVi.const_mul L)
  have hbound : ∀ x, ρ x * V x ≤ g x := fun x => young_five_thirds hK (hρ0 x) (hV0 x)
  have hprodi : Integrable (fun x => ρ x * V x) μ := by
    refine hgi.mono' (hρm.mul hVm) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ0 x) (hV0 x))]
    exact hbound x
  have hint : ∫ x, ρ x * V x ∂μ ≤ ∫ x, g x ∂μ :=
    integral_mono hprodi hgi hbound
  have hg_eval : ∫ x, g x ∂μ
      = K * (∫ x, ρ x ^ (5/3 : ℝ) ∂μ) + L * ∫ x, V x ^ (5/2 : ℝ) ∂μ := by
    rw [hg, integral_add (hρi.const_mul K) (hVi.const_mul L), integral_const_mul,
      integral_const_mul]
  rw [hg_eval] at hint
  linarith

/-- **The Legendre-duality reduction: eigenvalue form ⇒ kinetic-energy form.**

Suppose a state with one-particle density `ρ ≥ 0` and kinetic energy `T` satisfies the
Lieb–Thirring eigenvalue-sum bound with constant `L > 0`: for every nonnegative
measurable potential `V` with `V ^ (5/2)` integrable,
`T - ∫ ρ * V ≥ -L * ∫ V ^ (5/2)`.
Then it satisfies the Thomas–Fermi kinetic-energy bound
`ltKineticConst L * ∫ ρ ^ (5/3) ≤ T` with `ltKineticConst L = (3/5) * (2/(5*L)) ^ (2/3)`.

The proof is the optimal choice of trial potential `V = (2/(5*L)) ^ (2/3) * ρ ^ (2/3)`. -/
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
theorem ltDualConst_ltKineticConst {L : ℝ} (hL : 0 < L) :
    ltDualConst (ltKineticConst L) = L := by
  set b : ℝ := 2 / (5 * L) with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  have hK0 : 0 < ltKineticConst L := by rw [ltKineticConst, ← hb]; positivity
  have h1 : 5 * ltKineticConst L / 3 = b ^ (2/3 : ℝ) := by
    rw [ltKineticConst, ← hb]; ring
  have h2 : 3 / (5 * ltKineticConst L) = b ^ (-(2/3) : ℝ) := by
    rw [Real.rpow_neg hb0.le, ← h1]
    field_simp
  rw [ltDualConst, h2, ← Real.rpow_mul hb0.le,
    show (-((2:ℝ)/3)) * (3/2) = -1 by norm_num, Real.rpow_neg_one, hb]
  field_simp

end Frontier

