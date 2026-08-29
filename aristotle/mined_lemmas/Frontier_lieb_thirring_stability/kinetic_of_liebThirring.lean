/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory

/-- The Lieb–Thirring constant appearing in the kinetic energy inequality that is dual to
the Lieb–Thirring eigenvalue bound with constant `L` (in dimension `3`, exponent `γ = 1`). -/

theorem kinetic_of_liebThirring
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (ρ : α → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (T L : ℝ) (hL : 0 < L)
    (hint : Integrable (fun x => (ρ x) ^ ((5 : ℝ) / 3)) μ)
    (hLT : ∀ V : α → ℝ, (∀ x, 0 ≤ V x) →
        Integrable (fun x => V x * ρ x) μ →
        Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) μ →
        T - ∫ x, V x * ρ x ∂μ ≥ - L * ∫ x, (V x) ^ ((5 : ℝ) / 2) ∂μ) :
    T ≥ ltKineticConst L * ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ := by
  set a : ℝ := 2 / (5 * L) with ha_def
  have ha : 0 < a := by positivity
  set c : ℝ := a ^ ((2 : ℝ) / 3) with hc_def
  have hc : 0 < c := Real.rpow_pos_of_pos ha _
  set V : α → ℝ := fun x => c * (ρ x) ^ ((2 : ℝ) / 3) with hV_def
  have hVnn : ∀ x, 0 ≤ V x := fun x => mul_nonneg hc.le (Real.rpow_nonneg (hρ x) _)
  have h1 : ∀ x, V x * ρ x = c * (ρ x) ^ ((5 : ℝ) / 3) := by
    intro x
    have h : (ρ x) ^ ((2 : ℝ) / 3) * (ρ x) = (ρ x) ^ ((5 : ℝ) / 3) := by
      rw [show (5 : ℝ) / 3 = 2 / 3 + 1 by norm_num, Real.rpow_add' (hρ x) (by norm_num),
        Real.rpow_one]
    simp only [hV_def]
    rw [mul_assoc, h]
  have h2 : ∀ x, (V x) ^ ((5 : ℝ) / 2) = c ^ ((5 : ℝ) / 2) * (ρ x) ^ ((5 : ℝ) / 3) := by
    intro x
    simp only [hV_def]
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (hρ x) _), ← Real.rpow_mul (hρ x)]
    norm_num
  have hi1 : Integrable (fun x => V x * ρ x) μ := by
    simpa only [h1] using hint.const_mul c
  have hi2 : Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) μ := by
    simpa only [h2] using hint.const_mul (c ^ ((5 : ℝ) / 2))
  have key := hLT V hVnn hi1 hi2
  set X : ℝ := ∫ x, (ρ x) ^ ((5 : ℝ) / 3) ∂μ with hX_def
  have hX0 : 0 ≤ X := integral_nonneg (fun x => Real.rpow_nonneg (hρ x) _)
  rw [show (∫ x, V x * ρ x ∂μ) = c * X by simp only [h1]; rw [integral_const_mul],
      show (∫ x, (V x) ^ ((5 : ℝ) / 2) ∂μ) = c ^ ((5 : ℝ) / 2) * X by
        simp only [h2]; rw [integral_const_mul]] at key
  have hcpow : c ^ ((5 : ℝ) / 2) = a ^ ((5 : ℝ) / 3) := by
    rw [hc_def, ← Real.rpow_mul ha.le]; norm_num
  have hLa : L * a ^ ((5 : ℝ) / 3) = (2 / 5) * a ^ ((2 : ℝ) / 3) := by
    have h : a ^ ((5 : ℝ) / 3) = a ^ ((2 : ℝ) / 3) * a := by
      rw [show (5 : ℝ) / 3 = 2 / 3 + 1 by norm_num, Real.rpow_add' ha.le (by norm_num),
        Real.rpow_one]
    rw [h, ha_def]
    field_simp
  have hconst : c - L * c ^ ((5 : ℝ) / 2) = ltKineticConst L := by
    rw [hcpow, hLa, ltKineticConst, hc_def, ← ha_def]
    ring
  nlinarith [key, hX0, hconst]

/-- **The Lieb–Thirring hypothesis is satisfiable, with `ltKineticConst L` optimal.**
For any nonnegative density `ρ` with finite Thomas–Fermi energy, the value
`T = K_L ∫ ρ^(5/3)` already satisfies the variational Lieb–Thirring hypothesis. Combined
with `kinetic_of_liebThirring` (which gives `T ≥ K_L ∫ ρ^(5/3)`), this shows that the
constant `K_L` obtained by the duality argument cannot be improved, and in particular that
the hypotheses of the reduction are not vacuous. -/
