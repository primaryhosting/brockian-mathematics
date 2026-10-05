import Mathlib

/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Set

/-- The core computation: for `f, g` of class `C¹` with compact support, the function
`x ↦ x · f x · conj (g x)` is `C¹` with compact support, so the integral of its derivative
over `(0, ∞)` vanishes.  This is the integration-by-parts identity underlying symmetry of the
Berry–Keating dilation generator. -/

theorem symmetric_on_core_smooth (f g : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi 0) (hgs : tsupport g ⊆ Set.Ioi 0) :
    ∫ x in Set.Ioi (0:ℝ),
        (Complex.I * ((1/2) * f x + (x : ℂ) * deriv f x)) * starRingEnd ℂ (g x)
      = ∫ x in Set.Ioi (0:ℝ),
        f x * starRingEnd ℂ (Complex.I * ((1/2) * g x + (x : ℂ) * deriv g x)) :=
  symmetric_on_core_contDiff_one f g (hf.of_le (by exact_mod_cast le_top))
    (hg.of_le (by exact_mod_cast le_top)) hfc

end DilationGenerator
end Brockian

