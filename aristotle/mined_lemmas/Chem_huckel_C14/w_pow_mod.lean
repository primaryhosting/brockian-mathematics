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


lemma w_pow_mod (n : ℕ) : w ^ (n % 14) = w ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 14]
  rw [pow_add, pow_mul, w_pow_14, one_pow, one_mul]

/-- The additive character `k ↦ ω ^ k` of `Fin 14`. -/
