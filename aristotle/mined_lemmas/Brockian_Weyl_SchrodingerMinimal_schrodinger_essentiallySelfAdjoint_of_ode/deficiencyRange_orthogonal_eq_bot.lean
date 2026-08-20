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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

theorem deficiencyRange_orthogonal_eq_bot (V₀ : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (deficiencyRange V₀ z)ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hmem : MemLp ((w : ℝ → ℂ)) 2 volume := Lp.memLp w
  have key : ∀ f : ℝ → ℂ, IsTestFunction f →
      ∫ x, (starRingEnd ℂ) ((w : ℝ → ℂ) x) * (schrodingerExpr V₀ f x - z * f x) = 0 := by
    intro f hf
    have h1 : ccLp (fun x => schrodingerExpr V₀ f x - z * f x) ∈ deficiencyRange V₀ z :=
      ⟨f, hf, rfl⟩
    have h2 := (Submodule.mem_orthogonal _ _).1 hw _ h1
    rw [L2.inner_def] at h2
    have h3 : ∫ x, ((w : ℝ → ℂ) x)
        * (starRingEnd ℂ) ((ccLp (fun x => schrodingerExpr V₀ f x - z * f x) : ℝ → ℂ) x) = 0 := by
      rw [← h2]
      apply integral_congr_ae
      filter_upwards with x
      rw [RCLike.inner_apply]
    have h4 : (starRingEnd ℂ) (∫ x, ((w : ℝ → ℂ) x)
        * (starRingEnd ℂ)
          ((ccLp (fun x => schrodingerExpr V₀ f x - z * f x) : ℝ → ℂ) x)) = 0 := by
      rw [h3]; simp
    rw [← integral_conj] at h4
    rw [← h4]
    apply integral_congr_ae
    filter_upwards [ccLp_coe (memLp_expr V₀ z hf)] with x hx
    rw [map_mul, hx]
    simp [mul_comm]
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (weak_solution_eq_zero V₀ hz hmem key)

/-- For non-real `z`, the range of `τ - z` on test functions is dense in `L²(ℝ)`. -/
