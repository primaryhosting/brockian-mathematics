/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex (I)
open Matrix

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem ee_ne_one {d : Fin 19} (hd : d ≠ 0) : ee d ≠ 1 := by
  intro h
  have hdvd : (19 : ℕ) ∣ (d : ℕ) := (om_prim.pow_eq_one_iff_dvd _).mp h
  have hlt : (d : ℕ) < 19 := d.isLt
  have hpos : (d : ℕ) ≠ 0 := fun h0 => hd (Fin.val_eq_zero_iff.mp h0)
  omega

