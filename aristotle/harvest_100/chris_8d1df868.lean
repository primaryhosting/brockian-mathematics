/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/
noncomputable def zeta20 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

lemma zeta20_primitive : IsPrimitiveRoot zeta20 20 := by
  have h := Complex.isPrimitiveRoot_exp 20 (by norm_num)
  simpa [zeta20] using h

lemma zeta20_pow_20 : zeta20 ^ (20 : ℕ) = 1 := zeta20_primitive.pow_eq_one

lemma zeta20_pow_mod (x : ℕ) : zeta20 ^ (x % 20) = zeta20 ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 20]
  rw [pow_add, pow_mul, zeta20_pow_20, one_pow, one_mul]

/-- The additive character `m ↦ ζ^m` on `Fin 20`. -/
noncomputable def ec (m : Fin 20) : ℂ := zeta20 ^ (m : ℕ)

lemma ec_zero : ec 0 = 1 := by simp [ec]

lemma ec_add (a b : Fin 20) : ec (a + b) = ec a * ec b := by
  simp only [ec, Fin.val_add]
  rw [zeta20_pow_mod, pow_add]

lemma ec_neg (a : Fin 20) : ec (-a) = (ec a)⁻¹ := by
  have h : ec (-a) * ec a = 1 := by
    rw [← ec_add]
    simp [ec_zero]
  exact eq_inv_of_mul_eq_one_left h

lemma ec_mul_pow (m d : Fin 20) : ec (m * d) = (ec d) ^ (m : ℕ) := by
  simp only [ec, Fin.val_mul]
  rw [zeta20_pow_mod, mul_comm, pow_mul]

lemma ec_ne_one {d : Fin 20} (hd : d ≠ 0) : ec d ≠ 1 := by
  refine zeta20_primitive.pow_ne_one_of_pos_of_lt ?_ d.isLt
  simpa [Fin.val_eq_zero_iff] using hd

/-- `ζ^k + ζ^{-k} = 2 cos (2πk/20)`. -/
lemma ec_add_inv (k : Fin 20) :
    ec k + (ec k)⁻¹ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) := by
  have hexp : ec k = Complex.exp (((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    simp only [ec, zeta20]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hinv : (ec k)⁻¹ = Complex.exp (-((2 * Real.pi * (k : ℕ) / 20 : ℝ) : ℂ) * Complex.I) := by
    rw [hexp, ← Complex.exp_neg]
    congr 1
    ring
  rw [hinv, hexp, ← Complex.two_cos]
  push_cast [Complex.ofReal_cos]
  ring

/-! ### The Fourier (Vandermonde) matrix diagonalising the circulant -/

/-- The discrete Fourier matrix `F j k = ζ^{jk}`. -/
noncomputable def Fmat : Matrix (Fin 20) (Fin 20) ℂ := Matrix.of fun j k => ec (j * k)

/-- The (scaled) inverse Fourier matrix. -/
noncomputable def Gmat : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.of fun j k => (20 : ℂ)⁻¹ * (ec (j * k))⁻¹

lemma sum_ec_pow (d : Fin 20) :
    (∑ m : Fin 20, ec (m * d)) = if d = 0 then (20 : ℂ) else 0 := by
  have hrw : (∑ m : Fin 20, ec (m * d)) = ∑ i ∈ Finset.range 20, (ec d) ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (ec d) ^ i) 20]
    exact Finset.sum_congr rfl fun m _ => ec_mul_pow m d
  rw [hrw]
  by_cases hd : d = 0
  · subst hd
    simp [ec_zero]
  · rw [if_neg hd, geom_sum_eq (ec_ne_one hd)]
    have h20 : (ec d) ^ (20 : ℕ) = 1 := by
      rw [ec, ← pow_mul, mul_comm, pow_mul, zeta20_pow_20, one_pow]
    rw [h20, sub_self, zero_div]

lemma Fmat_mul_Gmat : Fmat * Gmat = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ m : Fin 20, Fmat j m * Gmat m k = (20 : ℂ)⁻¹ * ec (m * (j - k)) := by
    intro m
    simp only [Fmat, Gmat, Matrix.of_apply]
    rw [mul_sub, sub_eq_add_neg, ec_add, ec_neg, mul_comm m j]
    ring
  rw [Finset.sum_congr rfl fun m _ => hterm m, ← Finset.mul_sum, sum_ec_pow]
  by_cases h : j = k
  · subst h
    simp
  · rw [if_neg (by simpa [sub_eq_zero] using h)]
    rw [Matrix.one_apply_ne h]
    ring

lemma isUnit_Fmat : IsUnit Fmat := by
  have h2 : Gmat * Fmat = 1 := mul_eq_one_comm.mp Fmat_mul_Gmat
  exact ⟨⟨Fmat, Gmat, Fmat_mul_Gmat, h2⟩, rfl⟩

/-! ### The adjacency matrix of `C₂₀` -/

lemma cycle20_adj_iff (j m : Fin 20) :
    (SimpleGraph.cycleGraph 20).Adj j m ↔ (m = j - 1 ∨ m = j + 1) := by
  have h : (SimpleGraph.cycleGraph 20).Adj j m ↔ (j - m = 1 ∨ m - j = 1) :=
    SimpleGraph.cycleGraph_adj (n := 18)
  rw [h]
  constructor
  · rintro (h1 | h1)
    · left; rw [← h1]; abel
    · right; rw [← h1]; abel
  · rintro (h1 | h1) <;> subst h1
    · left; abel
    · right; abel

lemma adj_row_sum (g : Fin 20 → ℂ) (j : Fin 20) :
    (∑ m : Fin 20, ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) j m * g m)
      = g (j - 1) + g (j + 1) := by
  have hne : j - 1 ≠ j + 1 := by
    have h : ∀ i : Fin 20, i - 1 ≠ i + 1 := by decide
    exact h j
  have hterm : ∀ m : Fin 20,
      ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) j m * g m
        = if m ∈ ({j - 1, j + 1} : Finset (Fin 20)) then g m else 0 := by
    intro m
    rw [SimpleGraph.adjMatrix_apply]
    by_cases h : (SimpleGraph.cycleGraph 20).Adj j m
    · rw [if_pos h, one_mul, if_pos]
      simpa using (cycle20_adj_iff j m).mp h
    · rw [if_neg h, zero_mul, if_neg]
      intro hmem
      exact h ((cycle20_adj_iff j m).mpr (by simpa using hmem))
  rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair hne]

/-- The diagonal matrix of Hückel eigenvalues. -/
noncomputable def Dmat : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.diagonal fun k : Fin 20 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ)

/-- The key local identity: `ζ^{(j-1)k} + ζ^{(j+1)k} = 2cos(2πk/20) · ζ^{jk}`. -/
lemma ec_neighbour_sum (j k : Fin 20) :
    ec ((j - 1) * k) + ec ((j + 1) * k)
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) * ec (j * k) := by
  rw [← ec_add_inv k,
    show (j - 1) * k = j * k + (-k) by rw [sub_mul, one_mul, sub_eq_add_neg],
    show (j + 1) * k = j * k + k by rw [add_mul, one_mul],
    ec_add, ec_add, ec_neg]
  ring

lemma adj_mul_Fmat : (SimpleGraph.cycleGraph 20).adjMatrix ℂ * Fmat = Fmat * Dmat := by
  ext j k
  rw [Matrix.mul_apply, adj_row_sum (fun m => Fmat m k) j]
  simp only [Fmat, Dmat, Matrix.of_apply, Matrix.mul_diagonal, Matrix.of_apply]
  rw [ec_neighbour_sum j k]
  ring

/-! ### Main theorem -/

/-- **Hückel theory for C₂₀.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₂₀` (the Hückel matrix of the annulene C₂₀H₂₀, with `α = 0`, `β = 1`)
factors as `∏ (X - 2cos(2πk/20))`, i.e. its adjacency eigenvalues, with multiplicity,
are exactly `2·cos(2πk/20)` for `k = 0, …, 19`. -/
theorem huckel_C20 :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).charpoly
      = ∏ k : Fin 20,
          (Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ)) := by
  obtain ⟨U, hU⟩ := isUnit_Fmat
  have hA : (SimpleGraph.cycleGraph 20).adjMatrix ℂ = (U : Matrix (Fin 20) (Fin 20) ℂ) * Dmat *
      ((U⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
    have h1 : (SimpleGraph.cycleGraph 20).adjMatrix ℂ * (U : Matrix (Fin 20) (Fin 20) ℂ)
        = (U : Matrix (Fin 20) (Fin 20) ℂ) * Dmat := by
      rw [hU]; exact adj_mul_Fmat
    calc (SimpleGraph.cycleGraph 20).adjMatrix ℂ
        = (SimpleGraph.cycleGraph 20).adjMatrix ℂ * (U : Matrix (Fin 20) (Fin 20) ℂ) *
            ((U⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) : Matrix (Fin 20) (Fin 20) ℂ) := by
          rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      _ = _ := by rw [h1]
  rw [hA, Matrix.charpoly_units_conj U Dmat, Dmat, Matrix.charpoly_diagonal]

/-- The spectrum of the adjacency matrix of `C₂₀` is exactly the set of Hückel eigenvalues
`2·cos(2πk/20)`, `k = 0, …, 19`. -/
theorem huckel_C20_spectrum :
    spectrum ℂ ((SimpleGraph.cycleGraph 20).adjMatrix ℂ)
      = Set.range fun k : Fin 20 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) := by
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C20, Polynomial.IsRoot,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, (sub_eq_zero.mp (by simpa using hk)).symm⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ _, by simp [← hk]⟩

/-- The explicit Hückel molecular orbitals of C₂₀: for each `k`, the vector
`j ↦ exp(2πi jk/20)` is a nonzero eigenvector of the adjacency matrix with
eigenvalue `2·cos(2πk/20)`. -/
theorem huckel_C20_eigenvector (k : Fin 20) :
    (fun j : Fin 20 => ec (j * k)) ≠ 0 ∧
      ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) *ᵥ (fun j : Fin 20 => ec (j * k))
        = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) •
            (fun j : Fin 20 => ec (j * k)) := by
  constructor
  · intro h
    have h0 : ec ((0 : Fin 20) * k) = 0 := congrFun h 0
    rw [zero_mul, ec_zero] at h0
    exact one_ne_zero h0
  · funext j
    rw [Matrix.mulVec, dotProduct, adj_row_sum (fun m => ec (m * k)) j]
    simpa using ec_neighbour_sum j k

end Chem

