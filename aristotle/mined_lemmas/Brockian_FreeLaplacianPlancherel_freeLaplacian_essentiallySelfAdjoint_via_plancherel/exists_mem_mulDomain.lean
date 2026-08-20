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

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex
open scoped Real ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ## Essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A densely defined symmetric operator `T` with domain `D` in a complex Hilbert space is
*essentially self-adjoint* when both deficiency spaces are trivial, i.e. when the ranges of
`T + i` and `T - i` are dense. -/

lemma exists_mem_mulDomain (u : X → ℂ) (hu : Measurable u) (z : Lp ℂ 2 μ)
    (h1 : ∀ x, ‖u x‖ ≤ 1) (h2 : ∀ x, ‖(m x : ℂ) * u x‖ ≤ 1) :
    ∃ w : mulDomain m hm μ,
      ⇑(w : Lp ℂ 2 μ) =ᵐ[μ] (fun x => u x * z x) ∧
      ⇑(mulOp m hm μ w) =ᵐ[μ] (fun x => (m x : ℂ) * u x * z x) := by
  set g : X →ₘ[μ] ℂ := AEEqFun.mk u hu.aestronglyMeasurable * ((z : Lp ℂ 2 μ) : X →ₘ[μ] ℂ)
    with hg
  have hgcoe : ((g : X →ₘ[μ] ℂ) : X → ℂ) =ᵐ[μ] fun x => u x * z x := by
    rw [hg]
    filter_upwards [AEEqFun.coeFn_mul (AEEqFun.mk u hu.aestronglyMeasurable)
        ((z : Lp ℂ 2 μ) : X →ₘ[μ] ℂ), AEEqFun.coeFn_mk u hu.aestronglyMeasurable] with x hx hu'
    rw [hx]
    simp [hu']
  have hgmem : g ∈ Lp ℂ 2 μ := by
    refine mem_Lp_of_bound (z := z) ?_
    filter_upwards [hgcoe] with x hx
    rw [hx, norm_mul]
    calc ‖u x‖ * ‖z x‖ ≤ 1 * ‖z x‖ := by gcongr; exact h1 x
      _ = ‖z x‖ := one_mul _
  have hmem2 : mulSymbol m hm μ * g ∈ Lp ℂ 2 μ := by
    refine mem_Lp_of_bound (z := z) ?_
    filter_upwards [AEEqFun.coeFn_mul (mulSymbol m hm μ) g, coeFn_mulSymbol m hm μ, hgcoe]
      with x hx hs hz
    rw [hx]
    simp only [Pi.mul_apply, hs, hz]
    rw [← mul_assoc, norm_mul]
    calc ‖(m x : ℂ) * u x‖ * ‖z x‖ ≤ 1 * ‖z x‖ := by gcongr; exact h2 x
      _ = ‖z x‖ := one_mul _
  refine ⟨⟨⟨g, hgmem⟩, hmem2⟩, hgcoe, ?_⟩
  filter_upwards [coeFn_mulOp m hm μ ⟨⟨g, hgmem⟩, hmem2⟩, hgcoe] with x hx hz
  rw [hx]
  show (m x : ℂ) * ((g : X →ₘ[μ] ℂ) : X → ℂ) x = (m x : ℂ) * u x * z x
  rw [hz]
  ring

/-- The multiplication operator by a real function is symmetric. -/
