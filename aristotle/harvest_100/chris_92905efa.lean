/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency eigenvalues of the cycle graph `C n` (for `n ≥ 3`) are exactly
`2 cos (2πk/n)`, `k = 0, …, n-1`; these are the Hückel π-electron energies
(in units of the resonance integral `β`, measured from the Coulomb integral `α`).

The proof diagonalises the adjacency matrix by the discrete Fourier matrix
`F j k = ζ^(jk)` with `ζ = exp(2πi/n)`, and then uses `spectrum_diagonal`
(Mathlib, `Mathlib/LinearAlgebra/Eigenspace/Matrix.lean`) together with
`spectrum.units_conjugate`.
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- The primitive `n`-th root of unity `exp(2πi/n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := Complex.exp_ne_zero _

lemma isPrimitiveRoot_zeta {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

lemma zeta_pow_self {n : ℕ} (hn : n ≠ 0) : zeta n ^ n = 1 :=
  (isPrimitiveRoot_zeta hn).pow_eq_one

lemma zeta_pow_mod {n : ℕ} (hn : n ≠ 0) (x : ℕ) : zeta n ^ (x % n) = zeta n ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x n]
  rw [pow_add, pow_mul, zeta_pow_self hn, one_pow, one_mul]

lemma zeta_pow_inj {n : ℕ} (hn : n ≠ 0) {j l : Fin n}
    (h : zeta n ^ (j : ℕ) = zeta n ^ (l : ℕ)) : j = l :=
  Fin.ext ((isPrimitiveRoot_zeta hn).pow_inj j.isLt l.isLt h)

/-- The (unnormalised) discrete Fourier matrix `F j k = ζ ^ (j * k)`. -/
noncomputable def fourier (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => zeta n ^ ((j : ℕ) * (k : ℕ))

/-- The inverse of the discrete Fourier matrix. -/
noncomputable def fourierInv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => (n : ℂ)⁻¹ * (zeta n)⁻¹ ^ ((j : ℕ) * (k : ℕ))

/-- Orthogonality relation for the characters `k ↦ ζ ^ (j * k)`. -/
lemma sum_zeta_pow {n : ℕ} (hn : n ≠ 0) (j l : Fin n) :
    ∑ k : Fin n, zeta n ^ ((j : ℕ) * (k : ℕ)) * (zeta n)⁻¹ ^ ((k : ℕ) * (l : ℕ))
      = if j = l then (n : ℂ) else 0 := by
  set x : ℂ := zeta n ^ (j : ℕ) * (zeta n)⁻¹ ^ (l : ℕ) with hx
  have hterm : ∀ k : Fin n,
      zeta n ^ ((j : ℕ) * (k : ℕ)) * (zeta n)⁻¹ ^ ((k : ℕ) * (l : ℕ)) = x ^ (k : ℕ) := by
    intro k
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm (l : ℕ) (k : ℕ)]
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  have hxn : x ^ n = 1 := by
    rw [hx, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) n, mul_comm (l : ℕ) n,
      pow_mul, pow_mul, zeta_pow_self hn, inv_pow, zeta_pow_self hn]
    simp
  by_cases hjl : j = l
  · subst hjl
    have hx1 : x = 1 := by
      rw [hx, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ (zeta_ne_zero n))]
    simp [hx1]
  · have hx1 : x ≠ 1 := by
      intro h
      refine hjl (zeta_pow_inj hn ?_)
      rw [hx, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ (zeta_ne_zero n))] at h
      exact h
    rw [Fin.sum_univ_eq_sum_range (fun i => x ^ i) n, geom_sum_eq hx1, hxn]
    simp [hjl]

lemma fourier_mul_fourierInv {n : ℕ} (hn : n ≠ 0) : fourier n * fourierInv n = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hsplit : ∀ k : Fin n, fourier n j k * fourierInv n k l
      = (n : ℂ)⁻¹ * (zeta n ^ ((j : ℕ) * (k : ℕ)) * (zeta n)⁻¹ ^ ((k : ℕ) * (l : ℕ))) := by
    intro k; simp only [fourier, fourierInv, Matrix.of_apply]; ring
  rw [Finset.sum_congr rfl fun k _ => hsplit k, ← Finset.mul_sum, sum_zeta_pow hn]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  by_cases hjl : j = l <;> simp [hjl, Matrix.one_apply, hn']

/-- The `l`-th Hückel energy written as a sum of two roots of unity. -/
lemma two_cos_eq {n : ℕ} (hn : n ≠ 0) (l : Fin n) :
    ((2 * Real.cos (2 * Real.pi * (l : ℕ) / n) : ℝ) : ℂ)
      = zeta n ^ (l : ℕ) + zeta n ^ ((n - 1) * (l : ℕ)) := by
  have ha : zeta n ^ (l : ℕ) ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
  have hpow : zeta n ^ ((n - 1) * (l : ℕ)) = (zeta n ^ (l : ℕ))⁻¹ := by
    have hsum : zeta n ^ (l : ℕ) * zeta n ^ ((n - 1) * (l : ℕ)) = 1 := by
      rw [← pow_add]
      have he : (l : ℕ) + (n - 1) * (l : ℕ) = n * (l : ℕ) := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
      rw [he, pow_mul, zeta_pow_self hn, one_pow]
    field_simp
    linear_combination hsum
  rw [hpow]
  have hz : zeta n ^ (l : ℕ) = Complex.exp (((2 * Real.pi * (l : ℕ) / n : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hz, ← Complex.exp_neg, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- The adjacency matrix of the cycle graph is diagonalised by the Fourier matrix. -/
lemma adjMatrix_mul_fourier {n : ℕ} (hn : 3 ≤ n) :
    (cycleGraph n).adjMatrix ℂ * fourier n
      = fourier n * Matrix.diagonal
        (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hn0 : m + 2 ≠ 0 := by omega
  ext j l
  rw [SimpleGraph.adjMatrix_mul_apply, Matrix.mul_diagonal, cycleGraph_neighborFinset]
  have hne : (j - 1 : Fin (m + 2)) ≠ j + 1 := by
    intro h
    have h1 : j = j + 1 + 1 := sub_eq_iff_eq_add.mp h
    rw [add_assoc] at h1
    have h2 : ((1 : Fin (m + 2)) + 1) = 0 := by simpa using h1.symm
    have h3 : ((1 : Fin (m + 2)) + 1).val = 2 % (m + 2) := by
      rw [Fin.val_add]
      norm_num [Fin.val_one]
    rw [h2, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at h3
    exact absurd h3 (by norm_num)
  rw [Finset.sum_pair hne]
  simp only [fourier, Matrix.of_apply]
  have hsucc : ((j + 1 : Fin (m + 2)) : ℕ) = ((j : ℕ) + 1) % (m + 2) := by
    simp [Fin.val_add]
  have hpred : ((j - 1 : Fin (m + 2)) : ℕ) = ((j : ℕ) + (m + 1)) % (m + 2) := by
    rw [Fin.sub_def]
    simp only [Fin.val_one]
    congr 1
    omega
  have e1 : zeta (m + 2) ^ (((j + 1 : Fin (m + 2)) : ℕ) * (l : ℕ))
      = zeta (m + 2) ^ ((j : ℕ) * (l : ℕ)) * zeta (m + 2) ^ (l : ℕ) := by
    rw [hsucc]
    calc zeta (m + 2) ^ ((((j : ℕ) + 1) % (m + 2)) * (l : ℕ))
        = zeta (m + 2) ^ (((((j : ℕ) + 1) % (m + 2)) * (l : ℕ)) % (m + 2)) := by
          rw [zeta_pow_mod hn0]
      _ = zeta (m + 2) ^ (((((j : ℕ) + 1)) * (l : ℕ)) % (m + 2)) := by
          rw [Nat.mod_mul_mod]
      _ = zeta (m + 2) ^ ((((j : ℕ) + 1)) * (l : ℕ)) := zeta_pow_mod hn0 _
      _ = zeta (m + 2) ^ ((j : ℕ) * (l : ℕ)) * zeta (m + 2) ^ (l : ℕ) := by
          rw [← pow_add]; ring_nf
  have e2 : zeta (m + 2) ^ (((j - 1 : Fin (m + 2)) : ℕ) * (l : ℕ))
      = zeta (m + 2) ^ ((j : ℕ) * (l : ℕ)) * zeta (m + 2) ^ ((m + 1) * (l : ℕ)) := by
    rw [hpred]
    calc zeta (m + 2) ^ ((((j : ℕ) + (m + 1)) % (m + 2)) * (l : ℕ))
        = zeta (m + 2) ^ (((((j : ℕ) + (m + 1)) % (m + 2)) * (l : ℕ)) % (m + 2)) := by
          rw [zeta_pow_mod hn0]
      _ = zeta (m + 2) ^ ((((j : ℕ) + (m + 1)) * (l : ℕ)) % (m + 2)) := by
          rw [Nat.mod_mul_mod]
      _ = zeta (m + 2) ^ (((j : ℕ) + (m + 1)) * (l : ℕ)) := zeta_pow_mod hn0 _
      _ = zeta (m + 2) ^ ((j : ℕ) * (l : ℕ)) * zeta (m + 2) ^ ((m + 1) * (l : ℕ)) := by
          rw [← pow_add]; ring_nf
  rw [e1, e2, two_cos_eq hn0 l]
  have hm1 : (m + 2 - 1) = m + 1 := by omega
  rw [hm1]
  ring

/-- **Hückel spectrum of the cycle graph.**
For `n ≥ 3`, the spectrum of the adjacency matrix of the cycle graph `C n` is exactly the set
`{2 cos (2πk/n) : k = 0, …, n-1}`. These are the Hückel π-orbital energies (in units of the
resonance integral `β`, relative to the Coulomb integral `α`). -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ ((cycleGraph n).adjMatrix ℂ)
      = Set.range (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)) := by
  have hn0 : n ≠ 0 := by omega
  have hFG : fourier n * fourierInv n = 1 := fourier_mul_fourierInv hn0
  have hGF : fourierInv n * fourier n = 1 := mul_eq_one_comm.mp hFG
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨fourier n, fourierInv n, hFG, hGF⟩
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)) with hD
  have hconj : (cycleGraph n).adjMatrix ℂ
      = (u : Matrix (Fin n) (Fin n) ℂ) * D * ((u⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) := by
    show (cycleGraph n).adjMatrix ℂ = fourier n * D * fourierInv n
    rw [← adjMatrix_mul_fourier hn, Matrix.mul_assoc, hFG, Matrix.mul_one]
  rw [hconj, spectrum.units_conjugate, hD, spectrum_diagonal]

end Chem

