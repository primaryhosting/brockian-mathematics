/-
  Aristotle target — GENERAL BOUNDED-V ⇒ LIMIT-POINT at ∞.

  The `Brockian.Weyl.LP` module proved the CONSTANT-potential case
  (`const_potential_isLimitPoint`). This is the genuine general case that was left
  OPEN: for any BOUNDED real potential V and any non-real spectral parameter λ, the
  Schrödinger equation −y″ + V y = λ y is in the limit-point case at ∞ (there is a
  solution that is NOT square-integrable near ∞). This is the ODE analysis link that,
  together with the verified radius dichotomy and the von Neumann criterion, closes
  Gate 1 for a bounded potential.

  Definitions are inlined so the file is self-contained (import Mathlib only).
-/
import Mathlib

open MeasureTheory Filter Topology

namespace Brockian.Weyl.BoundedVTarget

/-- `y` solves `−y″ + V y = λ y`, i.e. `y″ = (V − λ) y`, on all of ℝ (complex-valued,
real variable), with `y'` its derivative and `y''` its second derivative. -/
structure IsSolution (V : ℝ → ℝ) (lam : ℂ) (y y' y'' : ℝ → ℂ) : Prop where
  deriv1 : ∀ x, HasDerivAt y (y' x) x
  deriv2 : ∀ x, HasDerivAt y' (y'' x) x
  eqn    : ∀ x, y'' x = ((V x : ℂ) - lam) * y x

/-- `y` is square-integrable near `+∞` (from some point `a` on). -/

 theorem boundedV_isLimitPoint (V : ℝ → ℝ) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (lam : ℂ) (hlam : lam.im ≠ 0) :
    IsLimitPointAtInfty V lam
-/

end Brockian.Weyl.BoundedVTarget

