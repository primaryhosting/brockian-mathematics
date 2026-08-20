/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix SimpleGraph

namespace Chem

/-- The primitive 13-th root of unity `exp (2πi/13)`. -/

lemma sum_xi (m : Fin 13) : ∑ j : Fin 13, xi (j * m) = if m = 0 then 13 else 0 := by
  have h1 : ∑ j : Fin 13, xi (j * m) = ∑ i ∈ Finset.range 13, xi m ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => xi m ^ i) 13]
    exact Finset.sum_congr rfl fun j _ => xi_mul_eq_pow j m
  rw [h1]
  split_ifs with hm
  · subst hm
    simp [xi_zero]
  · have hval : m.val ≠ 0 := by simpa using hm
    have hcop : Nat.Coprime m.val 13 := by
      have hp : Nat.Prime 13 := by norm_num
      rw [Nat.coprime_comm]
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_
      have h13 := Nat.le_of_dvd (Nat.pos_of_ne_zero hval) hdvd
      have := m.isLt
      omega
    have hprim : IsPrimitiveRoot (xi m) 13 :=
      isPrimitiveRoot_zeta13.pow_of_coprime m.val hcop
    exact hprim.geom_sum_eq_zero (by norm_num)

/-- The adjacency operator of `C₁₃` acts on vectors as the sum over the two neighbours. -/
