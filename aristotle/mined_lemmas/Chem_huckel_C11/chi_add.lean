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

lemma chi_add (x y : ZMod 11) : chi (x + y) = chi x * chi y := by
  simp only [chi, ZMod.val_add, zeta_pow_mod, pow_add]

