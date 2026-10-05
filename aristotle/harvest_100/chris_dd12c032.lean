import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace

noncomputable section

namespace QPhys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- For an `L²` function, the integral of the squared norm is the square of the `L²` norm. -/
theorem integral_norm_sq_eq_norm_sq (f : Lp (α := V) H 2) :
    ∫ x : V, ‖(f : V → H) x‖ ^ 2 = ‖f‖ ^ 2 := by
  have h1 : (inner ℂ f f : ℂ) = ∫ a : V, (inner ℂ ((f : V → H) a) ((f : V → H) a) : ℂ) :=
    L2.inner_def f f
  simp_rw [inner_self_eq_norm_sq_to_K] at h1
  exact_mod_cast h1.symm

/-- **Parseval/Plancherel theorem.** The Fourier transform is an isometry of `L²`: for every
square-integrable function `f`, the total squared magnitude of its Fourier transform equals the
total squared magnitude of `f`.  (In quantum mechanics: the position-space and momentum-space
wave functions carry the same total probability.) -/
theorem parseval_fourier (f : Lp (α := V) H 2) :
    ∫ ξ : V, ‖((𝓕 f : Lp (α := V) H 2) : V → H) ξ‖ ^ 2 = ∫ x : V, ‖(f : V → H) x‖ ^ 2 := by
  rw [integral_norm_sq_eq_norm_sq, integral_norm_sq_eq_norm_sq, Lp.norm_fourier_eq]

/-- The Fourier transform on `L²` preserves the inner product (polarized form of Parseval). -/
theorem inner_fourier_eq_inner (f g : Lp (α := V) H 2) :
    ∫ ξ : V, (inner ℂ (((𝓕 f : Lp (α := V) H 2)) ξ) (((𝓕 g : Lp (α := V) H 2)) ξ) : ℂ)
      = ∫ x : V, (inner ℂ ((f : V → H) x) ((g : V → H) x) : ℂ) := by
  rw [← L2.inner_def, ← L2.inner_def, Lp.inner_fourier_eq]

/-- **Parseval's theorem in explicit integral form**, for Schwartz functions on the line:
the Fourier integral `𝓕 f ξ = ∫ x, exp (-2πi x ξ) f x` preserves the `L²` norm. -/
theorem parseval_fourier_integral (f : 𝓢(ℝ, ℂ)) :
    ∫ ξ : ℝ, ‖𝓕 (f : ℝ → ℂ) ξ‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  simpa [SchwartzMap.fourier_coe] using SchwartzMap.integral_norm_sq_fourier f

end QPhys

#print axioms QPhys.parseval_fourier
#print axioms QPhys.inner_fourier_eq_inner
#print axioms QPhys.parseval_fourier_integral

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

