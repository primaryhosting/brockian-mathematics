/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset Complex

noncomputable section

/-- A primitive 11-th root of unity. -/

lemma sum_chi_mul_ite (d : ZMod 11) :
    ∑ k : ZMod 11, chi (k * d) = if d = 0 then 11 else 0 := by
  by_cases h : d = 0
  · subst h; simp [chi_zero]
  · simp [h, sum_chi_mul d h]

