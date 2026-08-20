import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma ee_ne_one {m : Fin 11} (hm : m ≠ 0) : ee m ≠ 1 :=
  zeta_primitive.pow_ne_one_of_pos_of_lt (fun h => hm (Fin.ext h)) m.isLt

