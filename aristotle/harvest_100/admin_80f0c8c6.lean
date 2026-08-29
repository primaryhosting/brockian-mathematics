import Mathlib
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the first command in a file, so the header
comment above is placed immediately after the single `import Mathlib` line.)
-/

open Complex Matrix Finset

namespace Chem

/-- The standard primitive `n`-th root of unity `exp (2πi/n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The character `Fin n → ℂ`, `j ↦ exp (2πi j/n)`. -/
noncomputable def chi (n : ℕ) (j : Fin n) : ℂ := zeta n ^ (j : ℕ)

variable {n : ℕ}

lemma isPrimitiveRoot_zeta (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma zeta_pow_n (hn : n ≠ 0) : zeta n ^ n = 1 := (isPrimitiveRoot_zeta hn).pow_eq_one

lemma zeta_pow_mod (hn : n ≠ 0) (x : ℕ) : zeta n ^ (x % n) = zeta n ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x n]
  rw [pow_add, pow_mul, zeta_pow_n hn, one_pow, one_mul]

lemma chi_add [NeZero n] (a b : Fin n) : chi n (a + b) = chi n a * chi n b := by
  simp only [chi, Fin.val_add]
  rw [zeta_pow_mod (NeZero.ne n), pow_add]

lemma chi_zero [NeZero n] : chi n 0 = 1 := by simp [chi]

lemma chi_neg [NeZero n] (a : Fin n) : chi n (-a) = (chi n a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← chi_add, add_neg_cancel, chi_zero])

lemma chi_mul [NeZero n] (a b : Fin n) : chi n (a * b) = (chi n b) ^ (a : ℕ) := by
  simp only [chi, Fin.val_mul]
  rw [zeta_pow_mod (NeZero.ne n), mul_comm, pow_mul]

lemma chi_ne_one [NeZero n] {t : Fin n} (ht : t ≠ 0) : chi n t ≠ 1 := by
  refine (isPrimitiveRoot_zeta (NeZero.ne n)).pow_ne_one_of_pos_of_lt ?_ t.isLt
  simpa [Fin.val_eq_zero_iff] using ht

lemma chi_pow_n [NeZero n] (t : Fin n) : (chi n t) ^ n = 1 := by
  rw [chi, ← pow_mul, mul_comm, pow_mul, zeta_pow_n (NeZero.ne n), one_pow]

/-- Orthogonality relation for the characters `chi n`. -/
lemma sum_chi [NeZero n] (t : Fin n) :
    ∑ k : Fin n, chi n (k * t) = if t = 0 then (n : ℂ) else 0 := by
  have h : ∑ k : Fin n, chi n (k * t) = ∑ i ∈ Finset.range n, (chi n t) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (chi n t) ^ i) n]
    exact Finset.sum_congr rfl fun k _ => chi_mul k t
  rw [h]
  split_ifs with ht
  · subst ht
    simp [chi_zero]
  · rw [geom_sum_eq (chi_ne_one ht), chi_pow_n, sub_self, zero_div]

/-- The pair of conjugate characters sums to the Hückel eigenvalue `2 cos (2πk/n)`. -/
lemma chi_add_chi_neg [NeZero n] (k : Fin n) :
    chi n k + chi n (-k) = 2 * Real.cos (2 * Real.pi * (k : ℕ) / n) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set t : ℝ := 2 * Real.pi * (k : ℕ) / n with ht
  have hk : chi n k = Complex.exp ((t : ℂ) * Complex.I) := by
    simp only [chi, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast [ht]
    field_simp
  have hnk : chi n (-k) = Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
    rw [chi_neg, hk, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [hk, hnk, Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_cos]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The spectrum of a cycle-type circulant matrix: `A u v = 1` exactly when `v = u ± 1`. -/
theorem circulant_cycle_spectrum [NeZero n] (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ u v, A u v = (if v = u - 1 then 1 else 0) + (if v = u + 1 then 1 else 0)) :
    spectrum ℂ A = {z : ℂ | ∃ k < n, z = 2 * Real.cos (2 * Real.pi * k / n)} := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  set d : Fin n → ℂ := fun k => 2 * Real.cos (2 * Real.pi * (k : ℕ) / n) with hd
  set F : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun j k => chi n (j * k)) with hF
  set G : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun k l => (n : ℂ)⁻¹ * chi n (-(k * l))) with hG
  -- `F` is invertible, with inverse `G`
  have hFG : F * G = 1 := by
    ext j l
    rw [Matrix.mul_apply]
    have hterm : ∀ k : Fin n, F j k * G k l = (n : ℂ)⁻¹ * chi n (k * (j - l)) := by
      intro k
      simp only [hF, hG, Matrix.of_apply]
      rw [show k * (j - l) = j * k + -(k * l) by
        rw [mul_sub, mul_comm k j, sub_eq_add_neg], chi_add]
      ring
    rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, sum_chi]
    by_cases h : j = l
    · subst h
      rw [sub_self, if_pos rfl, inv_mul_cancel₀ hn, Matrix.one_apply_eq]
    · rw [if_neg (sub_ne_zero_of_ne h), mul_zero, Matrix.one_apply_ne h]
  -- the columns of `F` are eigenvectors
  have hAF : A * F = F * Matrix.diagonal d := by
    ext u k
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    have hsum : ∑ v, A u v * F v k = F (u - 1) k + F (u + 1) k := by
      simp only [hA, add_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_add_distrib]
      simp
    rw [hsum]
    simp only [hF, Matrix.of_apply, hd]
    rw [show (u - 1) * k = u * k + -k by rw [sub_mul, one_mul, sub_eq_add_neg],
      show (u + 1) * k = u * k + k by rw [add_mul, one_mul],
      chi_add, chi_add, ← chi_add_chi_neg k]
    ring
  haveI : Invertible F := invertibleOfRightInverse F G hFG
  set u : (Matrix (Fin n) (Fin n) ℂ)ˣ := unitOfInvertible F
  have h1 : (u : Matrix (Fin n) (Fin n) ℂ) = F := rfl
  have h2 : (u : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal d * (↑u⁻¹ : Matrix _ _ ℂ) = A := by
    rw [h1, ← hAF, mul_assoc, ← h1, u.mul_inv, mul_one]
  rw [← h2, spectrum.units_conjugate, spectrum_diagonal]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq, hd]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, k.isLt, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

/-- **Hückel cycle spectrum.**  For `n ≥ 3`, the adjacency eigenvalues of the cycle graph
`C_n` are exactly the numbers `2 cos (2πk/n)`, `k = 0, …, n-1` (the Hückel π-energy levels,
in units where `α = 0` and `β = 1`). -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ ((SimpleGraph.cycleGraph n).adjMatrix ℂ) =
      {z : ℂ | ∃ k < n, z = 2 * Real.cos (2 * Real.pi * k / n)} := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  refine circulant_cycle_spectrum _ (fun u v => ?_)
  have hne : (u : Fin (m + 3)) - 1 ≠ u + 1 := by
    intro h
    rw [sub_eq_add_neg] at h
    have h1 : (-1 : Fin (m + 3)) = 1 := add_left_cancel h
    have h2 := congrArg Fin.val h1
    simp at h2
  simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj]
  by_cases h1 : v = u - 1
  · subst h1
    rw [if_pos (Or.inl (sub_sub_cancel u 1)), if_pos rfl, if_neg hne, add_zero]
  · by_cases h2 : v = u + 1
    · subst h2
      rw [if_pos (Or.inr (add_sub_cancel_left u 1)), if_neg h1, if_pos rfl, zero_add]
    · rw [if_neg h1, if_neg h2, if_neg, add_zero]
      rintro (h | h)
      · exact h1 (by rw [← h, sub_sub_cancel])
      · exact h2 (by rw [← h, add_sub_cancel])

end Chem

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

