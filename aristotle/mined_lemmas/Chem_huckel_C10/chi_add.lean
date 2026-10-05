import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem chi_add (a b : ZMod 10) : chi (a + b) = chi a * chi b := by
  have h : chi (a + b) = chi (((a.val + b.val : ℕ) : ZMod 10)) := by congr 1
  rw [h, chi_natCast, pow_add, chi, chi]

