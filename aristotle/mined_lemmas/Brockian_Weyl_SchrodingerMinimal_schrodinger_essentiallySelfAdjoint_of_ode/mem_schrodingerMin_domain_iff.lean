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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate Real
open LinearPMap Submodule

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Essential self-adjointness -/

section Abstract

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A densely defined operator `A` is *essentially self-adjoint* when it is symmetric and its
adjoint is self-adjoint (equivalently, its closure is self-adjoint; equivalently, it has a
unique self-adjoint extension, see `unique_selfAdjoint_extension`). -/

theorem mem_schrodingerMin_domain_iff (V₀ : ℝ) (u : Lp ℂ 2 (@haarAddCircle T hT)) :
    u ∈ (schrodingerMin T V₀).domain ↔ ∃ (g : ℤ → ℂ) (s : Finset ℤ), u = trigPolyL T g s := by
  constructor
  · intro hu
    rw [schrodingerMin, diagMin_domain, coe_fourierBasis] at hu
    obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu
    exact ⟨c, c.support, by rw [← hc, trigPolyL, Finsupp.sum]⟩
  · rintro ⟨g, s, rfl⟩
    exact trigPolyL_mem_domain T V₀ g s

/-- The minimal operator multiplies the `n`-th Fourier coefficient by the ODE eigenvalue. -/
