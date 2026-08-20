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

theorem schrodingerMin_apply_eq_ode (V₀ : ℝ) (g : ℤ → ℂ) (s : Finset ℤ) :
    ⇑(trigPolyL T g s) =ᵐ[haarAddCircle] ⇑(trigPolyC T g s) ∧
      ⇑(schrodingerMin T V₀ ⟨trigPolyL T g s, trigPolyL_mem_domain T V₀ g s⟩) =ᵐ[haarAddCircle]
        ⇑(trigPolyC T (fun n => (eig T V₀ n : ℂ) * g n) s) ∧
      ∀ x : ℝ, -(deriv (deriv fun y : ℝ => trigPolyC T g s (y : AddCircle T)) x)
          + (V₀ : ℂ) * trigPolyC T g s (x : AddCircle T)
        = trigPolyC T (fun n => (eig T V₀ n : ℂ) * g n) s (x : AddCircle T) :=
  ⟨coeFn_trigPolyL T g s, by
    rw [schrodingerMin_trigPolyL]; exact coeFn_trigPolyL T _ s,
   trigPolyC_ode T V₀ g s⟩

/-- **The minimal Schrödinger operator on the circle is essentially self-adjoint.** -/
