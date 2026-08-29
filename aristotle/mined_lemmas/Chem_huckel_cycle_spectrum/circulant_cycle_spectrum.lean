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
