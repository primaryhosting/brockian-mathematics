/-
# Singular Series Gaps 16021610
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps16021610
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

/-- A finite set of integers `H` is *admissible* if, for every prime `p`, the elements of `H`
do not cover all residue classes modulo `p`.  Equivalently (by the Euler-product formula for
the singular series `𝔖(H) = ∏_p (1 - ν_p(H)/p)(1 - 1/p)^{-|H|}`), the singular series attached
to `H` is non-zero, so that the Hardy–Littlewood prime `k`-tuple conjecture predicts infinitely
many translates of `H` consisting entirely of primes. -/

theorem subset_gapTuple_of_admissible (H : Finset ℤ) (hsub : H ⊆ Finset.Icc (1602 : ℤ) 1610)
    (hadm : Admissible H) (hlo : (1602 : ℤ) ∈ H) (hhi : (1610 : ℤ) ∈ H) :
    H ⊆ gapTuple16021610 := by
  obtain ⟨r2, hr2⟩ := hadm 2 (by norm_num)
  obtain ⟨r3, hr3⟩ := hadm 3 (by norm_num)
  have e2 : r2 = 1 := missed_class_two r2 (hr2 1602 hlo)
  have e3 : r3 = 1 := missed_class_three r3 (hr3 1602 hlo) (hr3 1610 hhi)
  subst e2; subst e3
  intro h hh
  have hA := hr2 h hh
  have hB := hr3 h hh
  have hmem := Finset.mem_Icc.1 (hsub hh)
  obtain ⟨hl, hu⟩ := hmem
  interval_cases h <;> revert hA hB <;> decide

/-- Consequently the gap range admits no admissible configuration of more than four elements
spanning `[1602, 1610]`. -/
