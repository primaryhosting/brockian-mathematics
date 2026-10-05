import Mathlib
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
In Hückel molecular orbital theory the π-energies of an annulene `C_n H_n` are `α + β λ`,
where `λ` runs over the eigenvalues of the adjacency matrix of the cycle graph `C n`.
This file proves that this spectrum is exactly `{2 cos (2 π k / n) : k = 0, …, n-1}`.

The proof diagonalizes the (circulant) adjacency matrix by the Vandermonde/Fourier matrix
built from the `n`-th roots of unity.
-/

open scoped BigOperators Real

namespace Chem

open SimpleGraph Matrix Complex

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with entries in `ℂ`:
the `(i, j)` entry is `1` when `i` and `j` are adjacent in `C n`, and `0` otherwise. -/
noncomputable def huckelAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if (SimpleGraph.cycleGraph n).Adj i j then 1 else 0

/-- The `n`-th root of unity used to diagonalize the circulant Hückel matrix. -/
noncomputable def omegaC (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The Fourier / Vandermonde matrix diagonalizing circulant matrices. -/
noncomputable def fourierMat (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vandermonde (fun i : Fin n => (omegaC n) ^ i.val)

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2 π k / n)`. -/
noncomputable def huckelDiag (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ))

section

variable {n : ℕ}

lemma omegaC_pow_n (hn : n ≠ 0) : (omegaC n) ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

/-- If `ζ ^ n = 1`, then `ζ ^ (m % n) = ζ ^ m`. -/
lemma pow_mod_eq {ζ : ℂ} (hζ : ζ ^ n = 1) (m : ℕ) : ζ ^ (m % n) = ζ ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hζ, one_pow, one_mul]

/-- `a ↦ ζ ^ a.val` is additive on `Fin n` when `ζ ^ n = 1`. -/
lemma pow_val_add {ζ : ℂ} (hζ : ζ ^ n = 1) (a b : Fin n) :
    ζ ^ ((a + b : Fin n)).val = ζ ^ a.val * ζ ^ b.val := by
  have h : ((a + b : Fin n)).val = (a.val + b.val) % n := rfl
  rw [h, pow_mod_eq hζ, pow_add]

/-- Euler's formula in the form `ω ^ k + (ω ^ k)⁻¹ = 2 cos (2 π k / n)`. -/
lemma omegaC_pow_add_inv (hn : n ≠ 0) (k : ℕ) :
    (omegaC n) ^ k + ((omegaC n) ^ k)⁻¹
      = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [omegaC, ← Complex.exp_nat_mul, ← Complex.exp_neg]
  push_cast
  rw [Complex.two_cos]
  congr 2 <;> field_simp

variable [NeZero n]

/-- Summing a function against the row of the adjacency matrix of `C n` picks out the two
neighbours `i - 1` and `i + 1`. -/
lemma sum_adj_eq (hn : 3 ≤ n) (i : Fin n) (f : Fin n → ℂ) :
    ∑ j, (if (SimpleGraph.cycleGraph n).Adj i j then (1 : ℂ) else 0) * f j
      = f (i - 1) + f (i + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : ∀ j : Fin (m + 3), (if (cycleGraph (m + 3)).Adj i j then (1 : ℂ) else 0) * f j
      = if (cycleGraph (m + 3)).Adj i j then f j else 0 := by
    intro j; split <;> simp
  simp only [h1]
  rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter,
    SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair]
  intro h
  rw [sub_eq_add_neg] at h
  have h2 : (-1 : Fin (m + 3)) = 1 := add_left_cancel h
  have h3 := congrArg Fin.val h2
  simp [Fin.neg_def] at h3

/-- The vector `j ↦ ω ^ (k j)` is an eigenvector of the Hückel matrix of `C n`
with eigenvalue `2 cos (2 π k / n)`. -/
theorem huckelAdj_mulVec (hn : 3 ≤ n) (k : Fin n) :
    (huckelAdj n).mulVec (fun j : Fin n => (omegaC n) ^ (k.val * j.val))
      = fun j : Fin n =>
        ((2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) * (omegaC n) ^ (k.val * j.val) := by
  have hn0 : n ≠ 0 := by omega
  have hω : (omegaC n) ^ n = 1 := omegaC_pow_n hn0
  set ζ : ℂ := (omegaC n) ^ k.val with hζdef
  have hζn : ζ ^ n = 1 := by
    rw [hζdef, ← pow_mul, mul_comm, pow_mul, hω, one_pow]
  have hpow : ∀ j : Fin n, (omegaC n) ^ (k.val * j.val) = ζ ^ j.val := by
    intro j; rw [hζdef, ← pow_mul]
  have hone : ((1 : Fin n)).val = 1 := by
    have : (1 : Fin n).val = 1 % n := rfl
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hneg : ((-1 : Fin n)).val = n - 1 := by
    have : ((-1 : Fin n)).val = (n - (1 : Fin n).val) % n := rfl
    rw [this, hone, Nat.mod_eq_of_lt (by omega)]
  have hinv : ζ ^ (n - 1) = ζ⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ]
    have : n - 1 + 1 = n := by omega
    rw [this, hζn]
  funext i
  simp only [Matrix.mulVec, dotProduct, huckelAdj]
  rw [sum_adj_eq hn i (fun j => (omegaC n) ^ (k.val * j.val))]
  simp only [hpow]
  rw [sub_eq_add_neg, pow_val_add hζn i (-1), pow_val_add hζn i 1, hone, hneg, hinv, pow_one]
  have hcos := omegaC_pow_add_inv (n := n) hn0 k.val
  rw [← hζdef] at hcos
  rw [show ζ ^ i.val * ζ⁻¹ + ζ ^ i.val * ζ = (ζ + ζ⁻¹) * ζ ^ i.val by ring, hcos]

omit [NeZero n] in
lemma fourierMat_det_ne_zero (hn : 3 ≤ n) : (fourierMat n).det ≠ 0 := by
  have hn0 : n ≠ 0 := by omega
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j hij
  exact Fin.ext ((Complex.isPrimitiveRoot_exp n hn0).pow_inj i.isLt j.isLt hij)

lemma huckelAdj_mul_fourier (hn : 3 ≤ n) :
    huckelAdj n * fourierMat n = fourierMat n * huckelDiag n := by
  ext i k
  have hvec := congrFun (huckelAdj_mulVec hn k) i
  simp only [Matrix.mulVec, dotProduct] at hvec
  rw [Matrix.mul_apply, huckelDiag, Matrix.mul_diagonal, fourierMat, Matrix.vandermonde_apply]
  have hcomm : ∀ j : Fin n, ((omegaC n) ^ j.val) ^ k.val = (omegaC n) ^ (k.val * j.val) := by
    intro j; rw [← pow_mul, mul_comm]
  simp only [Matrix.vandermonde_apply, hcomm]
  rw [hvec]
  ring

end

/-- **Hückel spectrum of the cycle graph.**
For `n ≥ 3`, the spectrum of the adjacency (Hückel) matrix of the cycle graph `C n` is exactly
`{2 cos (2 π k / n) : k = 0, …, n - 1}`. -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ (huckelAdj n)
      = Set.range (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ)) := by
  haveI : NeZero n := ⟨by omega⟩
  have hunit : IsUnit (fourierMat n) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (fourierMat_det_ne_zero hn))
  obtain ⟨u, hu⟩ := hunit
  have key : (u : Matrix (Fin n) (Fin n) ℂ) * huckelDiag n * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ)
      = huckelAdj n := by
    rw [hu, ← huckelAdj_mul_fourier hn, mul_assoc, ← hu, u.mul_inv, mul_one]
  rw [← key, spectrum.units_conjugate, huckelDiag, spectrum_diagonal]

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

