/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma sum_shift (g : ZMod 14 → ℂ) (c : ZMod 14) : ∑ j : ZMod 14, g (j + c) = ∑ j, g j :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

/-- Orthogonality / geometric sum for the character `ch`. -/
