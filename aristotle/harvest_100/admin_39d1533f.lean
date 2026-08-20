/-
/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The adjacency (Hückel) matrix of the cycle graph `C n` is diagonalised by the discrete Fourier
matrix `U j k = ζ ^ (j * k)`, `ζ = exp (2πi/n)`; its eigenvalues are the Hückel π-energies
`2 cos (2πk/n)`, `k = 0, …, n-1`.
-/

namespace Chem

open Complex Polynomial Matrix Finset

variable {n : ℕ}

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/
noncomputable def cyZeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The Hückel (adjacency) matrix of the cycle graph `C n`. -/
noncomputable def huckelMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (SimpleGraph.cycleGraph n).adjMatrix ℂ

/-- The discrete Fourier matrix `U j k = ζ ^ (j * k)`. -/
noncomputable def cyDFT (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => cyZeta n ^ ((j : ℕ) * (k : ℕ))

/-- The inverse of the discrete Fourier matrix, `V k l = n⁻¹ * ζ ^ (-(k * l))`. -/
noncomputable def cyDFTInv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun k l => (n : ℂ)⁻¹ * (cyZeta n ^ ((k : ℕ) * (l : ℕ)))⁻¹

lemma cyZeta_pow_n (hn : n ≠ 0) : cyZeta n ^ n = 1 :=
  (Complex.isPrimitiveRoot_exp n hn).pow_eq_one

lemma cyZeta_ne_zero : cyZeta n ≠ 0 := Complex.exp_ne_zero _

/-- Shifting the index by one in `Fin n` multiplies a power of an `n`-th root of unity by it. -/
lemma pow_succ_fin [NeZero n] (z : ℂ) (hz : z ^ n = 1) (j : Fin n) :
    z ^ ((j + 1 : Fin n) : ℕ) = z ^ (j : ℕ) * z := by
  have hmod : ∀ a : ℕ, z ^ (a % n) = z ^ a := by
    intro a
    conv_rhs => rw [← Nat.div_add_mod a n]
    rw [pow_add, pow_mul, hz, one_pow, one_mul]
  have hv : ((j + 1 : Fin n) : ℕ) = ((j : ℕ) + 1) % n := by
    rw [Fin.val_add, Fin.val_one']
    conv_rhs => rw [Nat.add_mod]
    simp [Nat.add_mod]
  rw [hv, hmod, pow_succ]

/-- The Fourier matrix is invertible, with explicit inverse `cyDFTInv`. -/
lemma cyDFT_mul_inv (hn : n ≠ 0) : cyDFT n * cyDFTInv n = 1 := by
  have hprim := Complex.isPrimitiveRoot_exp n hn
  have hw : cyZeta n ^ n = 1 := hprim.pow_eq_one
  have hpow : ∀ a : ℕ, (cyZeta n ^ a) ^ n = 1 := by
    intro a; rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
  ext j l
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin n, cyDFT n j k * cyDFTInv n k l
      = (n : ℂ)⁻¹ * (cyZeta n ^ (j : ℕ) * (cyZeta n ^ (l : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    simp only [cyDFT, cyDFTInv, mul_pow, inv_pow, ← pow_mul, mul_comm (k : ℕ) (l : ℕ)]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  set z : ℂ := cyZeta n ^ (j : ℕ) * (cyZeta n ^ (l : ℕ))⁻¹ with hz
  have hzn : z ^ n = 1 := by
    rw [hz, mul_pow, hpow, inv_pow, hpow, inv_one, one_mul]
  by_cases hjl : j = l
  · subst hjl
    have hz1 : z = 1 := by
      rw [hz]
      field_simp [pow_ne_zero _ (Complex.exp_ne_zero (2 * Real.pi * Complex.I / n)), cyZeta]
    rw [hz1]
    simp [Matrix.one_apply_eq, hn]
  · have hzne : z ≠ 1 := by
      rw [hz, ne_eq, mul_inv_eq_one₀ (pow_ne_zero _ (cyZeta_ne_zero (n := n)))]
      intro h
      exact hjl (Fin.ext (hprim.pow_inj j.isLt l.isLt h))
    have hsum : ∑ k : Fin n, z ^ (k : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range fun k => z ^ k, geom_sum_eq hzne, hzn, sub_self, zero_div]
    rw [hsum, mul_zero, Matrix.one_apply_ne hjl]

/-- The Fourier matrix diagonalises the Hückel matrix of the cycle. -/
lemma huckel_mul_cyDFT (hn : 3 ≤ n) :
    huckelMatrix n * cyDFT n =
      cyDFT n * diagonal (fun k : Fin n => cyZeta n ^ (k : ℕ) + (cyZeta n ^ (k : ℕ))⁻¹) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  ext j k
  rw [Matrix.mul_diagonal]
  have h1 : (huckelMatrix (m + 3) * cyDFT (m + 3)) j k
      = ∑ u ∈ (SimpleGraph.cycleGraph (m + 3)).neighborFinset j, cyDFT (m + 3) u k := by
    rw [huckelMatrix, Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct] using
      (SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (G := SimpleGraph.cycleGraph (m + 3)) j
        fun u => cyDFT (m + 3) u k)
  have hne : (j - 1 : Fin (m + 3)) ≠ j + 1 := by
    simp only [ne_eq, sub_eq_iff_eq_add, add_assoc j, left_eq_add]
    exact ne_of_beq_false rfl
  rw [h1, SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne]
  set w : ℂ := cyZeta (m + 3) with hwdef
  set c : ℂ := w ^ (k : ℕ) with hc
  have hwn : w ^ (m + 3) = 1 := cyZeta_pow_n (by omega)
  have hcn : c ^ (m + 3) = 1 := by rw [hc, ← pow_mul, mul_comm, pow_mul, hwn, one_pow]
  have hc0 : c ≠ 0 := by rw [hc]; exact pow_ne_zero _ cyZeta_ne_zero
  have hval : ∀ u : Fin (m + 3), cyDFT (m + 3) u k = c ^ (u : ℕ) := by
    intro u; rw [hc, ← pow_mul, mul_comm (k : ℕ) (u : ℕ)]; rfl
  rw [hval, hval, hval]
  have hplus : c ^ ((j + 1 : Fin (m + 3)) : ℕ) = c ^ (j : ℕ) * c := pow_succ_fin c hcn j
  have hminus : c ^ ((j - 1 : Fin (m + 3)) : ℕ) = c ^ (j : ℕ) * c⁻¹ := by
    have h := pow_succ_fin c hcn (j - 1)
    rw [sub_add_cancel] at h
    rw [eq_mul_inv_iff_mul_eq₀ hc0]
    exact h.symm
  rw [hplus, hminus]
  ring

/-- The `k`-th eigenvalue `ζ^k + ζ^(-k)` is the Hückel π-energy `2 cos (2πk/n)`. -/
lemma diag_eq_cos (k : Fin n) :
    cyZeta n ^ (k : ℕ) + (cyZeta n ^ (k : ℕ))⁻¹
      = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  have h : cyZeta n ^ (k : ℕ) = Complex.exp (2 * Real.pi * k / n * Complex.I) := by
    rw [cyZeta, ← Complex.exp_nat_mul]
    ring_nf
  rw [h, ← Complex.exp_neg]
  push_cast
  rw [Complex.cos]
  ring_nf

/-- **Hückel spectrum of the cycle graph.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C n` (`n ≥ 3`) factors as `∏ k, (X - 2 cos (2πk/n))`; i.e. its
eigenvalues, with multiplicity, are the Hückel π-energies `2 cos (2πk/n)`, `k = 0, …, n-1`. -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ).charpoly =
      ∏ k : Fin n, (X - C ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ)) := by
  have hn0 : n ≠ 0 := by omega
  set D : Matrix (Fin n) (Fin n) ℂ :=
    diagonal (fun k : Fin n => cyZeta n ^ (k : ℕ) + (cyZeta n ^ (k : ℕ))⁻¹) with hD
  have hUV : cyDFT n * cyDFTInv n = 1 := cyDFT_mul_inv hn0
  have hVU : cyDFTInv n * cyDFT n = 1 := mul_eq_one_comm.mp hUV
  have hA : huckelMatrix n = cyDFT n * (D * cyDFTInv n) := by
    have h := huckel_mul_cyDFT hn
    calc huckelMatrix n = huckelMatrix n * (cyDFT n * cyDFTInv n) := by rw [hUV, mul_one]
      _ = huckelMatrix n * cyDFT n * cyDFTInv n := by rw [mul_assoc]
      _ = cyDFT n * D * cyDFTInv n := by rw [h]
      _ = cyDFT n * (D * cyDFTInv n) := by rw [mul_assoc]
  have hchar : (huckelMatrix n).charpoly = D.charpoly := by
    rw [hA, Matrix.charpoly_mul_comm, mul_assoc, hVU, mul_one]
  rw [show ((SimpleGraph.cycleGraph n).adjMatrix ℂ) = huckelMatrix n from rfl, hchar, hD,
    Matrix.charpoly_diagonal]
  exact Finset.prod_congr rfl fun k _ => by rw [diag_eq_cos k]

/-- Consequently, a complex number is an eigenvalue of the Hückel matrix of `C n` exactly when
it is one of the energies `2 cos (2πk/n)`. -/
theorem huckel_cycle_eigenvalues (n : ℕ) (hn : 3 ≤ n) (r : ℂ) :
    r ∈ spectrum ℂ ((SimpleGraph.cycleGraph n).adjMatrix ℂ) ↔
      ∃ k : Fin n, r = ((2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot.def, huckel_cycle_spectrum n hn]
  simp [Polynomial.eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

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

