import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma isPrimitiveRoot_omega13 : IsPrimitiveRoot omega13 13 :=
  Complex.isPrimitiveRoot_exp 13 (by norm_num)

/-- The character `j ↦ ω^j` of `ZMod 13`. -/
