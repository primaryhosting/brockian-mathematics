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

lemma geom_sum_zeta_eq_zero (m : ℕ) (h : m % 8 ≠ 0) :
    ∑ j : Fin 8, zeta ^ ((j : ℕ) * m) = 0 := by
  set z : ℂ := zeta ^ m with hz
  have hz8 : z ^ 8 = 1 := by
    rw [hz, ← pow_mul, mul_comm, pow_mul, zeta_pow_eight, one_pow]
  have hzne : z ≠ 1 := by
    intro hcon
    have hdvd : (8 : ℕ) ∣ m := (zeta_isPrimitiveRoot.pow_eq_one_iff_dvd m).1 (hz ▸ hcon)
    omega
  have hsum : (z - 1) * (∑ j : Fin 8, z ^ (j : ℕ)) = 0 := by
    rw [Fin.sum_univ_eight]
    have : (z - 1) * (z ^ 0 + z ^ 1 + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 + z ^ 7)
        = z ^ 8 - 1 := by ring
    rw [show ((0 : Fin 8) : ℕ) = 0 from rfl]
    simpa [hz8] using this
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.2 hzne
  have hfin : ∑ j : Fin 8, z ^ (j : ℕ) = 0 := by
    rcases mul_eq_zero.1 hsum with h1 | h1
    · exact absurd h1 hzsub
    · exact h1
  calc ∑ j : Fin 8, zeta ^ ((j : ℕ) * m) = ∑ j : Fin 8, z ^ (j : ℕ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hz, ← pow_mul, mul_comm m (j : ℕ)]
    _ = 0 := hfin

