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

lemma abs_sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    |∑ i ∈ s, f i * g i| ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  refine abs_le.2 ⟨?_, Real.sum_mul_le_sqrt_mul_sqrt s f g⟩
  have h := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => -f i) g
  simp only [neg_mul, Finset.sum_neg_distrib, even_two.neg_pow] at h
  linarith

/-- Splitting the cosine kernel: the bilinear form of `cosKernel f g` decomposes as a
sum of two rank-one terms. -/
