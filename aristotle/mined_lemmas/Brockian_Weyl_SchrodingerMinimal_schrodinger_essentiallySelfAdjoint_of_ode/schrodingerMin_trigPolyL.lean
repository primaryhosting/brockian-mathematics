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

theorem schrodingerMin_trigPolyL (V₀ : ℝ) (g : ℤ → ℂ) (s : Finset ℤ) :
    schrodingerMin T V₀ ⟨trigPolyL T g s, trigPolyL_mem_domain T V₀ g s⟩
      = trigPolyL T (fun n => (eig T V₀ n : ℂ) * g n) s := by
  have hsub : (⟨trigPolyL T g s, trigPolyL_mem_domain T V₀ g s⟩ :
        (schrodingerMin T V₀).domain)
      = ∑ n ∈ s, g n • (⟨fourierLp 2 n, fourierLp_mem_domain T V₀ n⟩ :
        (schrodingerMin T V₀).domain) := by
    apply Subtype.ext
    simp [trigPolyL]
  rw [hsub]
  show (schrodingerMin T V₀).toFun _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [_root_.map_smul]
  show g n • (schrodingerMin T V₀) ⟨fourierLp 2 n, fourierLp_mem_domain T V₀ n⟩ = _
  rw [schrodingerMin_apply_fourier, smul_smul, mul_comm]

omit hT in
/-- **The ODE, for a trigonometric polynomial.** The classical differential expression
`-u'' + V₀ u` applied to a trigonometric polynomial multiplies its `n`-th coefficient by the
eigenvalue `eig T V₀ n`. -/
