/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset Complex

noncomputable section

/-- A primitive 11-th root of unity. -/

lemma sum_chi : ∑ x : ZMod 11, chi x = 0 := by
  have h : ∑ x : ZMod 11, chi x = ∑ i ∈ Finset.range 11, zeta ^ i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_nbij' (fun x => (⟨x.val, x.val_lt⟩ : Fin 11)) (fun i => (i.val : ZMod 11))
      (by intros; simp) (by intros; simp)
      (by intro a _; simp)
      (by intro a _; ext; simp [ZMod.val_natCast_of_lt a.isLt])
      (by intro a _; simp [chi])
  rw [h]
  have hprim := Complex.isPrimitiveRoot_exp 11 (by norm_num)
  have : zeta ≠ 1 := by
    intro hz
    have := hprim.ne_one (by norm_num)
    exact this (by simpa [zeta] using hz)
  have hgeom : (zeta - 1) * ∑ i ∈ Finset.range 11, zeta ^ i = zeta ^ 11 - 1 :=
    (geom_sum_mul zeta 11) ▸ (mul_comm _ _)
  rw [zeta_pow_eleven, sub_self] at hgeom
  rcases mul_eq_zero.1 hgeom with h1 | h2
  · exact absurd (sub_eq_zero.1 h1) this
  · exact h2

