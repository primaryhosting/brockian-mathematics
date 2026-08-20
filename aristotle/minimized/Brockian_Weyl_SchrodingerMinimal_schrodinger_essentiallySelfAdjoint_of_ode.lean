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

noncomputable def eig (V₀ : ℝ) (n : ℤ) : ℝ := (2 * π * n / T) ^ 2 + V₀

omit hT in
/-- **The ODE.** The `n`-th Fourier mode solves the Schrödinger eigenvalue equation
`-u'' + V₀ u = eig n * u` on the line. -/

theorem fourier_ode (V₀ : ℝ) (n : ℤ) (x : ℝ) :
    -(deriv (deriv fun y : ℝ => fourier n (y : AddCircle T)) x)
        + (V₀ : ℂ) * fourier n (x : AddCircle T)
      = (eig T V₀ n : ℂ) * fourier n (x : AddCircle T) := by
  have h1 : ∀ y : ℝ, HasDerivAt (fun z : ℝ => fourier n (z : AddCircle T))
      (2 * π * Complex.I * n / T * fourier n (y : AddCircle T)) y := hasDerivAt_fourier T n
  have hd1 : (deriv fun z : ℝ => fourier n (z : AddCircle T))
      = fun y : ℝ => 2 * π * Complex.I * n / T * fourier n (y : AddCircle T) :=
    funext fun y => (h1 y).deriv
  have hd2 : deriv (fun y : ℝ => 2 * π * Complex.I * n / T * fourier n (y : AddCircle T)) x
      = 2 * π * Complex.I * n / T * (2 * π * Complex.I * n / T * fourier n (x : AddCircle T)) :=
    ((h1 x).const_mul _).deriv
  rw [hd1, hd2, eig]
  push_cast
  linear_combination (-((2 * π * (n : ℂ) / T) ^ 2) * fourier n (x : AddCircle T)) * Complex.I_sq

/-- The minimal Schrödinger operator `-d²/dx² + V₀` on the circle `ℝ / Tℤ`: it is defined on the
span of the Fourier modes (the trigonometric polynomials), where it acts on each mode by the
eigenvalue produced by the ODE `fourier_ode`. -/
