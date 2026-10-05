import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma chi_add (a b : ZMod 15) : chi (a + b) = chi a * chi b := by
  obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective b
  rw [← Nat.cast_add, chi_natCast, chi_natCast, chi_natCast, pow_add]

