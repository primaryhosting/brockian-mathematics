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


lemma P_mul_Q : P14 * Q14 = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hstep : ∀ k : Fin 14, P14 j k * Q14 k l = (14 : ℂ)⁻¹ * zeta (k * (j - l)) := by
    intro k
    have hz : zeta (j * k) * zeta (-(k * l)) = zeta (k * (j - l)) := by
      rw [← zeta_add, fin14_mul_sub]
    rw [P14, Q14, show zeta (j * k) * ((14 : ℂ)⁻¹ * zeta (-(k * l)))
        = (14 : ℂ)⁻¹ * (zeta (j * k) * zeta (-(k * l))) by ring, hz]
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Finset.mul_sum, sum_zeta]
  by_cases h : j = l
  · subst h
    simp
  · have hne : j - l ≠ 0 := fun hc => h ((fin14_sub_eq_zero_iff j l).mp hc)
    rw [if_neg hne, Matrix.one_apply_ne h]
    ring

