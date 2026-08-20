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

lemma integral_deriv_weight_Ioi (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hg' : HasCompactSupport g) :
    ∫ x in Set.Ioi (0 : ℝ), deriv (weight f g) x = 0 := by
  rw [HasCompactSupport.integral_Ioi_deriv_eq (weight_contDiff hf hg)
    (weight_hasCompactSupport hg') 0]
  simp [weight]

/-- **Symmetry of the Berry–Keating dilation generator on the core `C_c^∞(0, ∞)`.**

For `f, g` smooth with compact support contained in `(0, ∞)`,
`∫ (A f) * conj g = ∫ f * conj (A g)` over `(0, ∞)`, where `A h = i * ((1/2) h + x h')`.

This is symmetry only; no self-adjointness claim is made.

Remark on hypotheses: the proof shows that the compact-support hypotheses alone suffice — the
requirement `tsupport f ⊆ Set.Ioi 0` (and likewise for `g`) is retained because it is part of the
requested statement, but it is not needed, since the boundary term `x * f x * conj (g x)` vanishes
at `x = 0` for trivial reasons. -/
