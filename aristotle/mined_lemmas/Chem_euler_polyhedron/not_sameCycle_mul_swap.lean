import Mathlib

/-!
# Counting the orbits of a permutation, and how a transposition changes the count

This file develops the basic combinatorial tool behind Euler's polyhedron formula:
for a permutation `f` of a finite type, multiplying by a transposition `swap x y`
either *merges* two orbits (if `x` and `y` lie in different orbits of `f`) or
*splits* one orbit into two (if `x` and `y` lie in the same orbit of `f`).
-/

open Equiv Equiv.Perm Function

namespace Polyhedron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of orbits (cycles, including fixed points) of a permutation of a finite type. -/

lemma not_sameCycle_mul_swap {f : Perm ι} {x y : ι} (hxy : x ≠ y) (h : f.SameCycle x y) :
    ¬ (f * swap x y).SameCycle x y := by
  classical
  set g := f * swap x y with hg
  have hex : ∃ n, 0 < n ∧ (f ^ n) y = x := by
    obtain ⟨i, _, hi⟩ := (h.symm).exists_pow_eq' (f := f)
    refine ⟨i, ?_, hi⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [pow_zero, Perm.one_apply] at hi
      exact absurd hi.symm hxy
    · exact hi0
  set k := Nat.find hex with hk
  obtain ⟨hkpos, hkx⟩ := Nat.find_spec hex
  have hstep : ∀ j, 0 < j → j < k → (f ^ j) y ≠ x ∧ (f ^ j) y ≠ y := by
    intro j hj hjk
    refine ⟨fun hjx => absurd ⟨hj, hjx⟩ (Nat.find_min hex hjk), fun hjy => ?_⟩
    have hkj : (f ^ (k - j)) y = x := by
      have hsum : k - j + j = k := by omega
      have h2 : (f ^ (k - j)) ((f ^ j) y) = x := by
        rw [← Perm.mul_apply, ← pow_add, hsum, hkx]
      rwa [hjy] at h2
    exact absurd ⟨by omega, hkj⟩ (Nat.find_min hex (by omega))
  have hgk : (g ^ k) x = x := by
    rw [hg, pow_mul_swap_apply hstep k hkpos le_rfl, hkx]
  set Q : ι → Prop := fun u => ∃ j : ℕ, j < k ∧ (g ^ j) x = u with hQ
  have hQx : Q x := ⟨0, hkpos, by simp⟩
  have hQg : ∀ u, Q u → Q (g u) := by
    rintro u ⟨j, hj, rfl⟩
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hlt | heq
    · exact ⟨j + 1, hlt, by rw [pow_succ']; rfl⟩
    · refine ⟨0, hkpos, ?_⟩
      have heq' : j + 1 = k := heq
      have h1 : (g ^ (j + 1)) x = g ((g ^ j) x) := by rw [pow_succ']; rfl
      rw [heq', hgk] at h1
      simpa using h1
  have hQginv : ∀ u, Q u → Q (g⁻¹ u) := by
    rintro u ⟨j, hj, rfl⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · refine ⟨k - 1, by omega, ?_⟩
      have h1 : g ((g ^ (k - 1)) x) = x := by
        have hk1 : k - 1 + 1 = k := by omega
        calc g ((g ^ (k - 1)) x) = (g ^ (k - 1 + 1)) x := by rw [pow_succ']; rfl
          _ = x := by rw [hk1, hgk]
      simp only [pow_zero, Perm.one_apply]
      exact eq_inv_iff_eq.mpr h1
    · refine ⟨j - 1, by omega, ?_⟩
      have h1 : g ((g ^ (j - 1)) x) = (g ^ j) x := by
        have hj1 : j - 1 + 1 = j := by omega
        calc g ((g ^ (j - 1)) x) = (g ^ (j - 1 + 1)) x := by rw [pow_succ']; rfl
          _ = (g ^ j) x := by rw [hj1]
      exact eq_inv_iff_eq.mpr h1
  have hQall : ∀ i : ℤ, Q ((g ^ i) x) := by
    intro i
    induction i using Int.induction_on with
    | zero => simpa using hQx
    | succ n ih =>
        have hgg : (g ^ ((n : ℤ) + 1)) x = g ((g ^ (n : ℤ)) x) := by
          rw [add_comm, zpow_one_add, Perm.mul_apply]
        rw [hgg]; exact hQg _ ih
    | pred n ih =>
        have hgg : (g ^ (-(n : ℤ) - 1)) x = g⁻¹ ((g ^ (-(n : ℤ))) x) := by
          rw [show (-(n : ℤ) - 1) = (-1) + (-(n : ℤ)) by ring, zpow_add, Perm.mul_apply,
            zpow_neg_one]
        rw [hgg]; exact hQginv _ ih
  rintro ⟨i, hi⟩
  obtain ⟨j, hj, hjx⟩ := hQall i
  rw [hi] at hjx
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [pow_zero, Perm.one_apply] at hjx
    exact hxy hjx
  · rw [hg, pow_mul_swap_apply hstep j hj0 (le_of_lt hj)] at hjx
    exact (hstep j hj0 hj).2 hjx

omit [Fintype ι] in
/-- Orbits of `f` are contained in orbits of `f * swap x y` when the latter merges
the orbits of `x` and `y`. -/
