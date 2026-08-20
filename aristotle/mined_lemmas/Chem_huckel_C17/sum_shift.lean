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

lemma sum_shift (F : ZMod 17 → ℂ) : ∑ j : ZMod 17, F (j + 1) = ∑ j : ZMod 17, F j :=
  Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

/-- Fourier coefficients of a vector. -/
