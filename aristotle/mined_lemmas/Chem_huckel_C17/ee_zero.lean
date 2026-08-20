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

lemma ee_zero : ee 0 = 1 := by simp [ee]

