/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`,
-- because Lean 4 requires all `import` commands to precede any command, including a module
-- docstring. The identical text is repeated below as the module docstring.)

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset

namespace Brockian

/-- The "cosine kernel" matrix `C i j = cos (f i - g j)`. -/

lemma bilin_cosKernel_eq {n : ℕ} (f g u v : Fin n → ℝ) :
    ∑ i, ∑ j, u i * Real.cos (f i - g j) * v j =
      (∑ i, u i * Real.cos (f i)) * (∑ j, v j * Real.cos (g j)) +
      (∑ i, u i * Real.sin (f i)) * (∑ j, v j * Real.sin (g j)) := by
  have h : ∀ i j : Fin n, u i * Real.cos (f i - g j) * v j =
      (u i * Real.cos (f i)) * (v j * Real.cos (g j)) +
      (u i * Real.sin (f i)) * (v j * Real.sin (g j)) := by
    intro i j
    rw [Real.cos_sub]; ring
  calc ∑ i, ∑ j, u i * Real.cos (f i - g j) * v j
      = ∑ i, ∑ j, ((u i * Real.cos (f i)) * (v j * Real.cos (g j)) +
          (u i * Real.sin (f i)) * (v j * Real.sin (g j))) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h i j
    _ = _ := by
        simp [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Pythagorean identity in sum form. -/
