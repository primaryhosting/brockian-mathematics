/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

lemma e5_pow_five (m : ZMod 5) : e5 m ^ 5 = 1 := by
  rw [← e5_nat_mul 5 m, show ((5 : ℕ) : ZMod 5) = 0 from by decide, zero_mul, e5_zero]

