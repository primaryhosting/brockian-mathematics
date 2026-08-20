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

noncomputable def deficiencyRange (V₀ : ℝ) (z : ℂ) :
    Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) where
  carrier := {v | ∃ f : ℝ → ℂ, IsTestFunction f ∧
    v = ccLp (fun x => schrodingerExpr V₀ f x - z * f x)}
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    refine ⟨fun x => f x + g x, isTestFunction_add hf hg, ?_⟩
    rw [← ccLp_add (memLp_expr V₀ z hf) (memLp_expr V₀ z hg)]
    congr 1
    funext x
    rw [schrodingerExpr_add V₀ hf.1 hg.1]
    ring
  zero_mem' := by
    refine ⟨0, ⟨contDiff_const, by
      simpa using (HasCompactSupport.zero : HasCompactSupport (fun _ : ℝ => (0 : ℂ)))⟩, ?_⟩
    have h0 : (fun x : ℝ => schrodingerExpr V₀ (0 : ℝ → ℂ) x - z * (0 : ℝ → ℂ) x)
        = fun _ : ℝ => (0 : ℂ) := by
      funext x; simp [schrodingerExpr]
    rw [h0, ccLp_zero]
  smul_mem' := by
    rintro c a ⟨f, hf, rfl⟩
    refine ⟨fun x => c * f x, isTestFunction_smul c hf, ?_⟩
    rw [← ccLp_smul c (memLp_expr V₀ z hf)]
    congr 1
    funext x
    rw [schrodingerExpr_smul V₀ c hf.1]
    ring

/-- The deficiency space is trivial: nothing in `L²` is orthogonal to the range of `τ - z`. -/
