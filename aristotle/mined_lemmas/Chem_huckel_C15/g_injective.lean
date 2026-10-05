import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma g_injective {i l : Fin 15} (h : g i = g l) : i = l :=
  Fin.ext (zeta_pow_inj i.isLt l.isLt h)

