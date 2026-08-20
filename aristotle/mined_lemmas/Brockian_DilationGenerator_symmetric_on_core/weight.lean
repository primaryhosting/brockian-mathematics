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

noncomputable def weight (f g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => (x : ℂ) * f x * (starRingEnd ℂ) (g x)

