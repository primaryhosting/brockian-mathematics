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

theorem schrodingerMin_apply_fourier (V₀ : ℝ) (n : ℤ) :
    schrodingerMin T V₀ ⟨fourierLp 2 n, by
      simpa [schrodingerMin, diagMin, coe_fourierBasis] using
        basis_mem_domain (fourierBasis (T := T)) (eig T V₀) n⟩
      = (eig T V₀ n : ℂ) • fourierLp 2 n := by
  have h := diagMin_apply_basis (fourierBasis (T := T)) (eig T V₀) n
  simpa only [coe_fourierBasis] using h

/-! ### The minimal operator really is the differential expression `-d²/dx² + V₀`

Its domain consists exactly of the trigonometric polynomials, and on such a function the operator
is computed by the classical differential expression applied to the (smooth) representative. -/

/-- A trigonometric polynomial, as a continuous function on the circle. -/
