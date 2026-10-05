/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

lemma sum_echar (c : Fin 11) :
    ∑ j : Fin 11, echar (j * c) = if c = 0 then (11 : ℂ) else 0 := by
  have hpow : ∀ j : Fin 11, echar (j * c) = (echar c) ^ (j : ℕ) := fun j => echar_mul j c
  rw [Finset.sum_congr rfl (fun j _ => hpow j)]
  by_cases hc : c = 0
  · subst hc
    simp [echar_zero]
  · rw [if_neg hc]
    have hne : echar c ≠ 1 := fun h => hc ((echar_eq_one_iff c).1 h)
    have hsum : ∑ j : Fin 11, (echar c) ^ (j : ℕ) = ∑ i ∈ Finset.range 11, (echar c) ^ i :=
      (Finset.sum_range fun i => (echar c) ^ i).symm
    rw [hsum, geom_sum_eq hne]
    have h11 : (echar c) ^ 11 = 1 := by
      rw [echar, ← pow_mul, mul_comm]
      rw [pow_mul, zeta11_pow_eleven, one_pow]
    rw [h11, sub_self, zero_div]

/-- The (unnormalized) discrete Fourier matrix. -/
