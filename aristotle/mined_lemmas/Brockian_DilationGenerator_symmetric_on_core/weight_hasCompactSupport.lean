import Mathlib
/-!
# Symmetric On Core
Category: Gate1 Operator
Target: Brockian.DilationGenerator.symmetric_on_core
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex

namespace Brockian
namespace DilationGenerator

variable {f g : ℝ → ℂ}

/-- The bilinear "boundary weight" `x ↦ x * f x * conj (g x)`, whose derivative is exactly the
combination of terms appearing in the difference of the two sides of the symmetry identity. -/

lemma weight_hasCompactSupport (hg : HasCompactSupport g) :
    HasCompactSupport (weight f g) := by
  have h : HasCompactSupport (fun x : ℝ => (starRingEnd ℂ) (g x)) :=
    hg.comp_left (g := starRingEnd ℂ) (map_zero _)
  exact HasCompactSupport.mul_left (f := fun x : ℝ => (x : ℂ) * f x) h

