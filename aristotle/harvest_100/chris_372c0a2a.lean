/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Complex

/-- A primitive 16-th root of unity. -/
noncomputable def zeta16 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of cyclic C₁₆,
with `α = 0`, `β = 1`). -/
noncomputable def C16adj : Matrix (Fin 16) (Fin 16) ℂ :=
  (SimpleGraph.cycleGraph 16).adjMatrix ℂ

/-- The claimed Hückel eigenvalues `2·cos(2πk/16)`, `k = 0, …, 15`. -/
noncomputable def huckelEigenvalue (k : Fin 16) : ℝ :=
  2 * Real.cos (2 * Real.pi * (k : ℕ) / 16)

/-- The `k`-th Fourier node `ζ₁₆ᵏ`. -/
noncomputable def node16 (k : Fin 16) : ℂ := zeta16 ^ (k : ℕ)

lemma isPrimitiveRoot_zeta16 : IsPrimitiveRoot zeta16 16 := by
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  norm_num at h
  simpa [zeta16] using h

lemma zeta16_pow_16 : zeta16 ^ 16 = 1 := isPrimitiveRoot_zeta16.pow_eq_one

lemma node16_pow_16 (k : Fin 16) : node16 k ^ 16 = 1 := by
  rw [node16, ← pow_mul, mul_comm, pow_mul, zeta16_pow_16, one_pow]

lemma node16_ne_zero (k : Fin 16) : node16 k ≠ 0 := by
  intro h
  have := node16_pow_16 k
  rw [h] at this
  norm_num at this

/-- For a 16-th root of unity, the exponent may be taken in `Fin 16`. -/
lemma pow_val_add {x : ℂ} (hx : x ^ 16 = 1) (a b : Fin 16) :
    x ^ ((a + b) : Fin 16).val = x ^ a.val * x ^ b.val := by
  have key : ∀ n : ℕ, x ^ (n % 16) = x ^ n := by
    intro n
    conv_rhs => rw [← Nat.div_add_mod n 16]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  rw [Fin.val_add, key, pow_add]

/-- The vertex-`i` entry of the `k`-th Fourier eigenvector. -/
lemma vandermonde_apply_eq (i k : Fin 16) :
    (Matrix.vandermonde node16) i k = node16 k ^ (i : ℕ) := by
  simp only [Matrix.vandermonde_apply, node16, ← pow_mul, mul_comm]

lemma node16_add_inv (k : Fin 16) :
    node16 k + node16 k ^ 15 = (huckelEigenvalue k : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 16 with ht
  have hx : node16 k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [node16, zeta16, ← Complex.exp_nat_mul]
    congr 1
    push_cast [ht]
    ring
  have hinv : node16 k ^ 15 = Complex.exp (-(t : ℂ) * Complex.I) := by
    have h16 : node16 k ^ 15 * node16 k = 1 := by
      rw [← pow_succ]; exact node16_pow_16 k
    have h2 : Complex.exp (-(t : ℂ) * Complex.I) * node16 k = 1 := by
      rw [hx, ← Complex.exp_add]
      simp
    exact mul_right_cancel₀ (node16_ne_zero k) (h16.trans h2.symm)
  rw [hinv, hx, huckelEigenvalue, ← ht]
  push_cast
  exact (Complex.two_cos _).symm

lemma adjMatrix_apply_iff (i j : Fin 16) :
    (SimpleGraph.cycleGraph 16).Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
  revert i j; decide

lemma sub_one_ne_add_one (i : Fin 16) : i - 1 ≠ i + 1 := by
  revert i; decide

lemma sum_over_neighbors (i : Fin 16) (v : Fin 16 → ℂ) :
    ∑ j, C16adj i j * v j = v (i - 1) + v (i + 1) := by
  have hstep : ∀ j : Fin 16, C16adj i j * v j
      = if j ∈ ({i - 1, i + 1} : Finset (Fin 16)) then v j else 0 := by
    intro j
    by_cases h : j = i - 1 ∨ j = i + 1
    · simp [C16adj, SimpleGraph.adjMatrix_apply, (adjMatrix_apply_iff i j).mpr h, h]
    · have hnot : ¬ (SimpleGraph.cycleGraph 16).Adj i j := fun hA =>
        h ((adjMatrix_apply_iff i j).mp hA)
      simp [C16adj, SimpleGraph.adjMatrix_apply, hnot, Finset.mem_insert,
        not_or.mp h |>.1, not_or.mp h |>.2]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_pair (sub_one_ne_add_one i)]

/-- The Fourier (Vandermonde/DFT) matrix conjugates the adjacency matrix of `C₁₆`
into the diagonal matrix of Hückel eigenvalues. -/
lemma C16adj_mul_vandermonde :
    C16adj * Matrix.vandermonde node16
      = Matrix.vandermonde node16 * Matrix.diagonal (fun k => (huckelEigenvalue k : ℂ)) := by
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_diagonal,
    sum_over_neighbors i (fun j => (Matrix.vandermonde node16) j k)]
  simp only [vandermonde_apply_eq]
  set x : ℂ := node16 k with hxdef
  have hx16 : x ^ 16 = 1 := node16_pow_16 k
  have h1 : x ^ ((i - 1 : Fin 16) : ℕ) = x ^ (i : ℕ) * x ^ 15 := by
    rw [sub_eq_add_neg, pow_val_add hx16 i (-1)]
    norm_num
  have h2 : x ^ ((i + 1 : Fin 16) : ℕ) = x ^ (i : ℕ) * x := by
    rw [pow_val_add hx16 i 1]
    norm_num
  rw [h1, h2, ← node16_add_inv k, ← hxdef]
  ring

lemma det_vandermonde_node16_ne_zero : (Matrix.vandermonde node16).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext (isPrimitiveRoot_zeta16.pow_inj a.isLt b.isLt hab)

/-- **Hückel theory for cyclic C₁₆.**  The adjacency matrix of the cycle graph `C₁₆` is
diagonalized by the discrete Fourier (Vandermonde) matrix, and its eigenvalues are exactly
`2·cos(2πk/16)` for `k = 0, 1, …, 15` (with multiplicity). -/
theorem huckel_C16 :
    ∃ U : Matrix (Fin 16) (Fin 16) ℂ, IsUnit U.det ∧
      U⁻¹ * C16adj * U = Matrix.diagonal (fun k : Fin 16 => ((huckelEigenvalue k : ℝ) : ℂ)) := by
  have hU : IsUnit (Matrix.vandermonde node16).det :=
    isUnit_iff_ne_zero.mpr det_vandermonde_node16_ne_zero
  refine ⟨Matrix.vandermonde node16, hU, ?_⟩
  rw [Matrix.mul_assoc, C16adj_mul_vandermonde, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]

/-- Each column of the Fourier matrix is an eigenvector of the `C₁₆` adjacency matrix with
eigenvalue `2·cos(2πk/16)`. -/
theorem huckel_C16_eigenvector (k : Fin 16) :
    C16adj *ᵥ (fun j : Fin 16 => node16 k ^ (j : ℕ))
      = ((huckelEigenvalue k : ℝ) : ℂ) • (fun j : Fin 16 => node16 k ^ (j : ℕ)) := by
  funext i
  have hx16 : node16 k ^ 16 = 1 := node16_pow_16 k
  have h1 : node16 k ^ ((i - 1 : Fin 16) : ℕ) = node16 k ^ (i : ℕ) * node16 k ^ 15 := by
    rw [sub_eq_add_neg, pow_val_add hx16 i (-1)]; norm_num
  have h2 : node16 k ^ ((i + 1 : Fin 16) : ℕ) = node16 k ^ (i : ℕ) * node16 k := by
    rw [pow_val_add hx16 i 1]; norm_num
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [sum_over_neighbors i (fun j => node16 k ^ (j : ℕ)), h1, h2, ← node16_add_inv k]
  ring

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

