/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Polynomial Matrix SimpleGraph Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The character `a ↦ exp (2πi a / n)` on `Fin n`. -/
noncomputable def ev {n : ℕ} (a : Fin n) : ℂ := zeta n ^ (a : ℕ)

/-- The `k`-th Hückel π-energy (in units where α = 0, β = 1) of the cycle `C n`. -/
noncomputable def huckelEigen (n : ℕ) (k : Fin n) : ℂ :=
  2 * (Real.cos (2 * Real.pi * (k : ℕ) / n) : ℂ)

section

variable {n : ℕ} [NeZero n]

lemma isPrimitiveRoot_zeta : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

lemma zeta_pow_self : zeta n ^ n = 1 := (isPrimitiveRoot_zeta (n := n)).pow_eq_one

lemma zeta_pow_mod (x : ℕ) : zeta n ^ (x % n) = zeta n ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x n]
  rw [pow_add, pow_mul, zeta_pow_self, one_pow, one_mul]

lemma ev_add (a b : Fin n) : ev (a + b) = ev a * ev b := by
  simp only [ev, Fin.val_add, ← pow_add, zeta_pow_mod]

lemma ev_zero : ev (0 : Fin n) = 1 := by simp [ev]

lemma ev_mul (a b : Fin n) : ev (a * b) = ev b ^ (a : ℕ) := by
  simp only [ev, Fin.val_mul, zeta_pow_mod, ← pow_mul, mul_comm]

lemma ev_ne_zero (a : Fin n) : ev a ≠ 0 := by
  simp only [ev]
  exact pow_ne_zero _ (Complex.exp_ne_zero _)

lemma ev_neg (a : Fin n) : ev (-a) = (ev a)⁻¹ := by
  have h : ev a * ev (-a) = 1 := by rw [← ev_add, add_neg_cancel, ev_zero]
  field_simp [ev_ne_zero a] at h ⊢
  linear_combination h

lemma ev_pow_card (a : Fin n) : ev a ^ n = 1 := by
  simp only [ev, ← pow_mul, mul_comm ((a : ℕ)) n, pow_mul, zeta_pow_self, one_pow]

lemma ev_eq_one_iff (a : Fin n) : ev a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have hdvd : n ∣ (a : ℕ) :=
      ((isPrimitiveRoot_zeta (n := n)).pow_eq_one_iff_dvd (a : ℕ)).1 h
    exact Fin.ext (Nat.eq_zero_of_dvd_of_lt hdvd a.isLt)
  · rintro rfl; exact ev_zero

/-- Orthogonality of the characters: `∑ k, ev (k * m)` is `n` if `m = 0` and `0` otherwise. -/
lemma sum_ev (m : Fin n) : ∑ k : Fin n, ev (k * m) = if m = 0 then (n : ℂ) else 0 := by
  have h : ∀ k : Fin n, ev (k * m) = ev m ^ (k : ℕ) := fun k => ev_mul k m
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun j => ev m ^ j) n]
  by_cases hm : m = 0
  · subst hm
    simp [ev_zero]
  · rw [if_neg hm, geom_sum_eq, ev_pow_card]
    · simp
    · intro hcon
      exact hm ((ev_eq_one_iff m).1 hcon)

lemma ev_add_ev_neg (a : Fin n) : ev a + ev (-a) = huckelEigen n a := by
  have hexp : ev a = Complex.exp ((2 * Real.pi * (a : ℕ) / n : ℝ) * Complex.I) := by
    rw [ev, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexp' : ev (-a) = Complex.exp (-((2 * Real.pi * (a : ℕ) / n : ℝ) * Complex.I)) := by
    rw [ev_neg, hexp, Complex.exp_neg]
  rw [hexp, hexp', huckelEigen, ← Complex.ofReal_cos, Complex.cos]
  push_cast
  ring

end

section Matrices

variable (n : ℕ) [NeZero n]

/-- The (unnormalised) discrete Fourier matrix, whose `k`-th column is the eigenvector of the
cycle adjacency matrix for the eigenvalue `huckelEigen n k`. -/
noncomputable def fourierMat : Matrix (Fin n) (Fin n) ℂ := fun i k => ev (i * k)

/-- The inverse of `fourierMat`. -/
noncomputable def fourierMatInv : Matrix (Fin n) (Fin n) ℂ :=
  fun k j => (n : ℂ)⁻¹ * ev (-(k * j))

lemma fourierMat_mul_inv : fourierMat n * fourierMatInv n = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : Fin n, fourierMat n i k * fourierMatInv n k j
      = (n : ℂ)⁻¹ * ev (k * (i - j)) := by
    intro k
    simp only [fourierMat, fourierMatInv]
    rw [show k * (i - j) = i * k + -(k * j) by ring, ev_add]
    ring
  simp only [h, ← Finset.mul_sum, sum_ev]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  by_cases hij : i = j
  · subst hij
    simp [hn]
  · rw [if_neg (by simpa [sub_eq_zero] using hij), Matrix.one_apply_ne hij]
    ring

lemma fourierMatInv_mul : fourierMatInv n * fourierMat n = 1 :=
  mul_eq_one_comm.1 (fourierMat_mul_inv n)

/-- `fourierMat` as a unit of the matrix ring. -/
noncomputable def fourierUnit : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := fourierMat n
  inv := fourierMatInv n
  val_inv := fourierMat_mul_inv n
  inv_val := fourierMatInv_mul n

end Matrices

section Cycle

variable {m : ℕ}

lemma cycle_adj_sum (w : Fin (m + 3) → ℂ) (i : Fin (m + 3)) :
    ∑ j, ((cycleGraph (m + 3)).adjMatrix ℂ) i j * w j = w (i - 1) + w (i + 1) := by
  have hne : (i - 1) ≠ (i + 1) := by
    intro h
    have h2 : ((i - 1 : Fin (m + 3)) : ℕ) = ((i + 1 : Fin (m + 3)) : ℕ) := by rw [h]
    have hs : (i - 1 : Fin (m + 3)) + 1 + 1 = i + 1 + 1 := by rw [h]
    have : (i : Fin (m + 3)) + 1 + 1 = i := by
      rw [← hs]; ring_nf; rw [sub_add_cancel]
    have hval : ((i + 1 + 1 : Fin (m + 3)) : ℕ) = (i : ℕ) := by rw [this]
    simp only [Fin.val_add, Fin.val_one] at hval
    omega
  have hsum : ∑ j, ((cycleGraph (m + 3)).adjMatrix ℂ) i j * w j
      = ∑ j ∈ (cycleGraph (m + 3)).neighborFinset i, w j := by
    rw [Finset.sum_congr rfl (g := fun j => if (cycleGraph (m + 3)).Adj i j then w j else 0)
      (by intro j _; by_cases h : (cycleGraph (m + 3)).Adj i j <;> simp [h])]
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp [SimpleGraph.mem_neighborFinset]
  rw [hsum]
  have : (cycleGraph (m + 1 + 2)).neighborFinset i = {i - 1, i + 1} :=
    SimpleGraph.cycleGraph_neighborFinset
  rw [show m + 3 = m + 1 + 2 from rfl] at *
  rw [this, Finset.sum_pair hne]

lemma adjMatrix_mul_fourierMat :
    ((cycleGraph (m + 3)).adjMatrix ℂ) * fourierMat (m + 3)
      = fourierMat (m + 3) * Matrix.diagonal (huckelEigen (m + 3)) := by
  ext i k
  rw [Matrix.mul_apply, cycle_adj_sum (fun j => fourierMat (m + 3) j k) i,
    Matrix.mul_diagonal]
  simp only [fourierMat]
  rw [show (i - 1) * k = i * k + -(1 * k) by ring, show (i + 1) * k = i * k + 1 * k by ring,
    ev_add, ev_add, one_mul, ← mul_add, ← ev_add_ev_neg k]
  ring

end Cycle

/-- **Hückel spectrum of the cycle graph.**  For `n ≥ 3`, the characteristic polynomial of the
adjacency matrix of the cycle graph `C n` factors as `∏ k, (X - 2cos(2πk/n))`, and consequently
its spectrum (set of eigenvalues) is exactly `{2cos(2πk/n) : k = 0, …, n-1}` — the Hückel
π-energies of the cyclic polyene. -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    ((cycleGraph n).adjMatrix ℂ).charpoly
        = ∏ k : Fin n, (X - C (2 * (Real.cos (2 * Real.pi * (k : ℕ) / n) : ℂ)))
      ∧ spectrum ℂ ((cycleGraph n).adjMatrix ℂ)
        = {μ : ℂ | ∃ k : Fin n, μ = 2 * (Real.cos (2 * Real.pi * (k : ℕ) / n) : ℂ)} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  haveI : NeZero (m + 3) := ⟨by omega⟩
  have hA : ((cycleGraph (m + 3)).adjMatrix ℂ)
      = (fourierUnit (m + 3) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ)
        * Matrix.diagonal (huckelEigen (m + 3))
        * ((fourierUnit (m + 3))⁻¹ : (Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ)ˣ) := by
    have h := adjMatrix_mul_fourierMat (m := m)
    calc ((cycleGraph (m + 3)).adjMatrix ℂ)
        = ((cycleGraph (m + 3)).adjMatrix ℂ) * (fourierMat (m + 3) * fourierMatInv (m + 3)) := by
          rw [fourierMat_mul_inv, mul_one]
      _ = (((cycleGraph (m + 3)).adjMatrix ℂ) * fourierMat (m + 3)) * fourierMatInv (m + 3) := by
          rw [mul_assoc]
      _ = _ := by rw [h]; rfl
  have hchar : ((cycleGraph (m + 3)).adjMatrix ℂ).charpoly
      = ∏ k : Fin (m + 3), (X - C (huckelEigen (m + 3) k)) := by
    rw [hA, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  refine ⟨hchar, ?_⟩
  ext μ
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hchar]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    sub_eq_zero, Set.mem_setOf_eq, huckelEigen]

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

