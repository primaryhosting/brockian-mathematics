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


lemma sum_zeta (m : Fin 14) : ∑ k : Fin 14, zeta (k * m) = if m = 0 then 14 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [zeta]
  · rw [if_neg hm]
    have hsum : ∑ k : Fin 14, zeta (k * m) = ∑ n ∈ range 14, (zeta m) ^ n := by
      rw [← Fin.sum_univ_eq_sum_range (fun n => (zeta m) ^ n) 14]
      exact Finset.sum_congr rfl fun k _ => zeta_mul k m
    have hmul : (∑ n ∈ range 14, (zeta m) ^ n) * (zeta m - 1) = 0 := by
      rw [geom_sum_mul, zeta_pow_14, sub_self]
    have hne : zeta m - 1 ≠ 0 := sub_ne_zero.mpr (zeta_ne_one hm)
    rw [hsum]
    exact (mul_eq_zero.mp hmul).resolve_right hne

/-! ### The adjacency matrix of `C₁₄` and its diagonalisation -/

/-- The adjacency matrix of the cycle graph `C₁₄`, over `ℂ`. -/
