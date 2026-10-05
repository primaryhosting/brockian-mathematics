/-
  RequestProject/ESA.lean

  Essential self-adjointness of the harmonic-oscillator core
  `harmonicOscillatorPMap` (the operator `-d²/dx² + x²` on the Schwartz core of
  `L²(ℝ)`).

  The argument is the classical deficiency-index one.  If `g` is in the domain of
  the adjoint with `T* g = z • g` and `Im z ≠ 0`, then pairing against the Hermite
  functions `hermiteFun n` (which lie in the Schwartz core and satisfy
  `H hermiteFun n = (2n+1) hermiteFun n`) forces `⟪g, hermiteFun n⟫ = 0` for every
  `n`, since `conj z ≠ 2n+1`.  The Hermite functions span every monomial
  `xⁿ e^{-x²/2}`, so all the moments of `x ↦ conj (g x) e^{-x²/2}` vanish, and the
  moment theorem gives `g = 0`.
-/
import RequestProject.Corpus
import RequestProject.Hermite
import RequestProject.Moments

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.Moments

/-! ### Integrability facts for an `L²` function against Gaussian weights -/


@[simp] theorem gaussianSchwartz_apply (x : ℝ) :
    gaussianSchwartz x = (Real.exp (-(x ^ 2 / 2)) : ℂ) := rfl

end Brockian.Gaussian

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
  RequestProject/Moments.lean

  A moment-vanishing theorem: a function on `ℝ` with uniform exponential
  integrability all of whose moments `∫ xⁿ G x` vanish is zero almost everywhere.

  The proof expands `exp (w x)` in its power series inside the integral (all the
  moments kill it), which shows that the Fourier transform of `G` vanishes
  identically; pairing against Schwartz test functions and using that the Fourier
  transform is onto the Schwartz space then gives `∫ φ G = 0` for every smooth
  compactly supported `φ`, whence `G = 0` a.e.
-/
import Mathlib

open MeasureTheory Complex Real Filter
open scoped FourierTransform ENNReal Nat

namespace Brockian.Moments

section

variable {G : ℝ → ℂ}
  (hmeas : AEStronglyMeasurable G volume)
  (hint : ∀ c : ℝ, Integrable (fun x : ℝ => ‖G x‖ * Real.exp (c * |x|)) volume)

include hmeas hint

/-- Under the exponential-integrability hypothesis, all the functions
`x ↦ xⁿ G x` are integrable. -/
