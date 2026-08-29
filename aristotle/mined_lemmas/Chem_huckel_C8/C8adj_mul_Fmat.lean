/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 4000000

namespace Chem

/-- A primitive 8-th root of unity. -/

lemma C8adj_mul_Fmat : C8adj * Fmat = Fmat * Matrix.diagonal mu := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  simp only [C8adj, Fmat, Fin.sum_univ_eight]
  fin_cases i <;>
    simp +decide [mu, mul_add, ← pow_add, ← Nat.succ_mul, ← Nat.add_mul] <;>
    ring_nf <;>
    simp [zeta_pow_mul_eight, zeta_pow_mul_nine, zeta_pow_mul_ten, zeta_pow_mul_eleven,
      zeta_pow_mul_twelve, zeta_pow_mul_thirteen, zeta_pow_mul_fourteen, add_comm]

/-- Geometric sum of a non-trivial power of `zeta` over a full period vanishes. -/
