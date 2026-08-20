/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Complex

/-! ### A primitive 17-th root of unity and the associated additive character -/

/-- A primitive 17-th root of unity. -/

lemma ee_neg (x : ZMod 17) : ee (-x) = (ee x)⁻¹ := by
  have h : ee x * ee (-x) = 1 := by rw [← ee_add]; simp [ee_zero]
  field_simp [ee_ne_zero]
  linear_combination h

