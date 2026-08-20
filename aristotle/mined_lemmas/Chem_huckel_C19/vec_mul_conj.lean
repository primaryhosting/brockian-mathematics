/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma vec_mul_conj : C19vec * C19conj = (19 : ℂ) • (1 : Matrix (ZMod 19) (ZMod 19) ℂ) := by
  ext i j
  set c : ℕ := (i.val + 18 * j.val) % 19 with hc
  set z : ℂ := om ^ c with hz
  have hterm : ∀ k : ZMod 19, C19vec i k * C19conj k j = z ^ k.val := by
    intro k
    rw [C19vec, C19conj, hz, ← pow_mul, ← pow_add]
    refine om_pow_congr ?_
    have hmod : c * k.val % 19 = ((i.val + 18 * j.val) * k.val) % 19 := by
      simp [hc, Nat.mul_mod]
    rw [hmod]
    congr 1
    ring
  have hsum : (C19vec * C19conj) i j = ∑ m ∈ Finset.range 19, z ^ m := by
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => hterm k)]
    exact Fin.sum_univ_eq_sum_range (fun m => z ^ m) 19
  rw [hsum]
  by_cases h : i = j
  · subst h
    have hc0 : c = 0 := by
      have := i.val_lt
      omega
    simp [hz, hc0]
  · have hcne : c ≠ 0 := by
      intro h0
      apply h
      apply ZMod.val_injective 19
      have hi := i.val_lt
      have hj := j.val_lt
      rw [hc] at h0
      omega
    have hzne : z ≠ 1 := om_prim.pow_ne_one_of_pos_of_lt hcne (by simp [hc]; omega)
    have hz19 : z ^ 19 = 1 := by
      rw [hz, ← pow_mul, mul_comm, pow_mul, om_pow_19, one_pow]
    rw [geom_sum_eq hzne, hz19, sub_self, zero_div]
    simp [h]

