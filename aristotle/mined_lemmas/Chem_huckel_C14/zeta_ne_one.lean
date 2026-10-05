import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph Matrix

namespace Chem

/-! ### Arithmetic in `Fin 14`

`Fin 14` carries the modular `+`, `-`, `*` and `-·` operations used by
`SimpleGraph.cycleGraph_adj`, but no `CommRing` instance is available for the numeral `14`,
so the handful of ring identities we need are checked by decision procedure. -/

section Fin14


lemma zeta_ne_one {m : Fin 14} (hm : m ≠ 0) : zeta m ≠ 1 := by
  refine w_primitive.pow_ne_one_of_pos_of_lt ?_ m.isLt
  simpa [Fin.val_eq_zero_iff] using hm

