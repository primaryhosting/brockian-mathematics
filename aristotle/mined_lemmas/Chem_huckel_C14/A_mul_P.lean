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


lemma A_mul_P : A14 * P14 = P14 * Matrix.diagonal lam := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ l : Fin 14, A14 j l * P14 l k = P14 (j - 1) k + P14 (j + 1) k := by
    simp [A_apply, add_mul, ite_mul, Finset.sum_add_distrib]
  have h1 : P14 (j - 1) k = zeta (j * k) * zeta (-k) := by
    rw [P14, fin14_pred_mul, zeta_add]
  have h2 : P14 (j + 1) k = zeta (j * k) * zeta k := by
    rw [P14, fin14_succ_mul, zeta_add]
  have hR : ∑ l : Fin 14, P14 j l * Matrix.diagonal lam l k = P14 j k * lam k := by
    simp [Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']
  rw [hL, h1, h2, hR, P14, ← zeta_add_neg k]
  ring

