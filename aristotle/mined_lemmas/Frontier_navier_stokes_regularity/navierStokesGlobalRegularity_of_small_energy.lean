import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
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

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

theorem navierStokesGlobalRegularity_of_small_energy (eps : ℝ) (heps : 0 < eps)
    (H : ∀ ν : ℝ, 0 < ν → ∀ U : SchwartzMap E3 E3, (∀ x, divg (⇑U) x = 0) →
      (∫ x : E3, ‖U x‖ ^ 2) < eps → SolvableData ν (⇑U)) :
    NavierStokesGlobalRegularity := by
  intro ν hν U hdiv
  set En : ℝ := ∫ x : E3, ‖U x‖ ^ 2 with hEn
  have hEn0 : 0 ≤ En := MeasureTheory.integral_nonneg fun x => by positivity
  set c : ℝ := En / eps + 1 with hcdef
  have hc : 0 < c := by
    have : 0 ≤ En / eps := div_nonneg hEn0 heps.le
    simp only [hcdef]; linarith
  have hUdiff : Differentiable ℝ (⇑U) := (U.smooth (⊤ : ℕ∞)).differentiable (by simp)
  -- the rescaled datum
  set V : SchwartzMap E3 E3 := scaledSchwartz c hc U with hV
  have hVdiv : ∀ x, divg (⇑V) x = 0 := by
    intro x
    have hVfun : (⇑V) = fun y => c • U (c • y) := by
      funext y; simp [hV]
    rw [hVfun, divg_comp_smul (⇑U) hUdiff c x, hdiv (c • x), mul_zero]
  have hVenergy : (∫ x : E3, ‖V x‖ ^ 2) < eps := by
    have hVfun : ∀ x : E3, ‖V x‖ ^ 2 = ‖c • U (c • x)‖ ^ 2 := by
      intro x; simp [hV]
    simp only [hVfun]
    rw [integral_norm_sq_scale (⇑U) hc, ← hEn]
    have hcne : c ≠ 0 := hc.ne'
    have hrw : c ^ 2 * ((c ^ 3)⁻¹ * En) = En / c := by
      field_simp
    rw [hrw, div_lt_iff₀ hc, hcdef]
    have : En / eps * eps = En := div_mul_cancel₀ En heps.ne'
    nlinarith [this]
  have hVsolv : SolvableData ν (⇑V) := H ν hν V hVdiv hVenergy
  have hback := solvableData_scale hVsolv (c := c⁻¹) (inv_pos.mpr hc)
  have hfun : (fun x => c⁻¹ • (⇑V) (c⁻¹ • x)) = (⇑U) := by
    funext x
    simp only [hV, scaledSchwartz_apply, smul_smul]
    rw [mul_inv_cancel₀ hc.ne', one_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rwa [hfun] at hback

/-! ## Main statement -/

/-- **Navier–Stokes regularity.**  The full formal statement of the three dimensional
incompressible Navier–Stokes global regularity problem (Clay Millennium Problem, zero external
force) is recorded as the definition `Frontier.NavierStokesGlobalRegularity`.  The theorem below
collects the three facts about it that are established here:

* the *base case*: the zero initial datum launches a global smooth finite energy solution;
* the *scaling invariance*: the class of solvable initial data is closed under the
  Navier–Stokes scaling `u₀ ↦ c u₀(c ·)`, `c > 0`;
* a Lean-checked *reduction*: for any `ε > 0`, global regularity for all divergence free
  Schwartz data of kinetic energy `< ε` already implies the full conjecture. -/
