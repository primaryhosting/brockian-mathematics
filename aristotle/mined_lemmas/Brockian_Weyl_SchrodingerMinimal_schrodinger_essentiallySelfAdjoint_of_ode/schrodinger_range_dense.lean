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

theorem schrodinger_range_dense (V₀ : ℝ) {z : ℂ} (hz : z.im ≠ 0) {w : ℝ → ℂ}
    (hw : MemLp w 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℂ, IsTestFunction f ∧
      eLpNorm (fun x => w x - (schrodingerExpr V₀ f x - z * f x)) 2 volume < ENNReal.ofReal ε := by
  have hbot := deficiencyRange_orthogonal_eq_bot V₀ hz
  have hclosure : (deficiencyRange V₀ z).topologicalClosure = ⊤ := by
    have h1 : (deficiencyRange V₀ z)ᗮᗮ = (deficiencyRange V₀ z).topologicalClosure :=
      Submodule.orthogonal_orthogonal_eq_closure _
    rw [hbot] at h1
    simpa using h1.symm
  have hdense : Dense ((deficiencyRange V₀ z : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)))
      : Set (Lp ℂ 2 (volume : Measure ℝ))) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure
  obtain ⟨v, hvS, hvd⟩ := Metric.mem_closure_iff.1 (hdense (hw.toLp w)) ε hε
  obtain ⟨f, hf, rfl⟩ := hvS
  refine ⟨f, hf, ?_⟩
  have hsub : MemLp (fun x => w x - (schrodingerExpr V₀ f x - z * f x)) 2 volume :=
    hw.sub (memLp_expr V₀ z hf)
  have heq : eLpNorm (fun x => w x - (schrodingerExpr V₀ f x - z * f x)) 2 volume
      = eLpNorm (⇑(hw.toLp w) - ⇑(ccLp (fun x => schrodingerExpr V₀ f x - z * f x))) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [hw.coeFn_toLp, ccLp_coe (memLp_expr V₀ z hf)] with x h1 h2
    simp [h1, h2]
  rw [heq]
  rw [Lp.dist_def] at hvd
  rw [ENNReal.lt_ofReal_iff_toReal_lt]
  · exact hvd
  · rw [← heq]; exact hsub.2.ne

/-! ## The ODE hypothesis, and its discharge -/

/-- The ODE hypothesis on which essential self-adjointness of the minimal Schrödinger
operator rests (the Weyl limit-point condition, in weak form): for non-real spectral
parameter `z`, no nonzero `L²` function solves `-u'' + V₀ u = z u` weakly.  Equivalently,
both deficiency spaces of the minimal operator are trivial. -/
