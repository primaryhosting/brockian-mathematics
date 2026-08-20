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

lemma chi_ne_zero (x : ZMod 11) : chi x ≠ 0 := by
  refine pow_ne_zero _ ?_
  simp [zeta, Complex.exp_ne_zero]

