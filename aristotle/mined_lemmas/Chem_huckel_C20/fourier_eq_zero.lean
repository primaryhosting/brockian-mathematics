import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma fourier_eq_zero (x : ZMod 20 → ℂ) (h : ∀ m < 20, ∑ j, evec m j * x j = 0) : x = 0 := by
  funext i
  have key : ∑ m ∈ range 20, w ^ (m * (-i).val) * (∑ j, evec m j * x j) = 20 * x i := by
    have hin : ∀ m ∈ range 20, w ^ (m * (-i).val) * (∑ j, evec m j * x j)
        = ∑ j, w ^ (m * (j - i).val) * x j := by
      intro m _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hval : (j - i : ZMod 20).val = (j.val + (-i).val) % 20 := by
        rw [sub_eq_add_neg, ZMod.val_add]
      have : w ^ (m * (-i).val) * w ^ (m * j.val) = w ^ (m * (j - i).val) := by
        rw [← pow_add]
        apply w_pow_mod
        rw [hval, Nat.mul_mod, Nat.mod_mod_of_dvd _ dvd_rfl, ← Nat.mul_mod]
        congr 1
        ring
      rw [evec, ← mul_assoc, this]
    have hcollapse : ∀ j : ZMod 20, ∑ m ∈ range 20, w ^ (m * (j - i).val) * x j
        = (if j = i then (20 : ℂ) else 0) * x j := by
      intro j
      rw [← Finset.sum_mul, geom_sum_w (j - i)]
      simp [sub_eq_zero]
    calc ∑ m ∈ range 20, w ^ (m * (-i).val) * (∑ j, evec m j * x j)
        = ∑ m ∈ range 20, ∑ j : ZMod 20, w ^ (m * (j - i).val) * x j :=
          Finset.sum_congr rfl hin
      _ = ∑ j : ZMod 20, ∑ m ∈ range 20, w ^ (m * (j - i).val) * x j := Finset.sum_comm
      _ = ∑ j : ZMod 20, (if j = i then (20 : ℂ) else 0) * x j :=
          Finset.sum_congr rfl fun j _ => hcollapse j
      _ = 20 * x i := by simp
  have hzero : ∑ m ∈ range 20, w ^ (m * (-i).val) * (∑ j, evec m j * x j) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [h m (Finset.mem_range.1 hm), mul_zero]
  rw [hzero] at key
  have h20 : (20 : ℂ) ≠ 0 := by norm_num
  simpa using (mul_eq_zero.1 key.symm).resolve_left h20

/-- Each Fourier coefficient of an eigenvector is killed unless the eigenvalue matches. -/
