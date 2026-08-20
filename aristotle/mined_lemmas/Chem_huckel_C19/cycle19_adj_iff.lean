/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

lemma cycle19_adj_iff (u v : Fin 19) :
    (cycleGraph 19).Adj u v ↔ (v = u + 1 ∨ v = u - 1) := by
  revert u v
  decide

/-- `C19adj` acts on the `k`-th Fourier column by multiplication by `2 cos (2πk/19)`. -/
