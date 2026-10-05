/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/

theorem ch_eq_exp (k : Fin 18) :
    ch k = Complex.exp (((2 * Real.pi * k.val / 18 : ℝ) : ℂ) * Complex.I) := by
  rw [ch, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

