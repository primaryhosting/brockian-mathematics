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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Hückel π-electron energy levels of benzene-like annulenes come from the adjacency
spectrum of a cycle graph.  Here we compute the spectrum of the cycle `C₁₂`: the
eigenvalues of its adjacency matrix are exactly `2 cos (2πk/12)` for `k = 0, …, 11`.

The proof diagonalises the (circulant) adjacency matrix by the discrete Fourier
transform: with `ζ = exp (2πi/12)` and `P i k = ζ^(i k)` (a Vandermonde matrix in the
powers of `ζ`) one has `A P = P D` with `D` diagonal with entries `2 cos (2πk/12)`,
and `P` is invertible since `ζ` is a primitive 12-th root of unity.

Main Mathlib inputs: `Complex.isPrimitiveRoot_exp`, `Matrix.det_vandermonde_eq_zero_iff`,
`Matrix.charpoly_units_conj`, `Matrix.charpoly_diagonal`,
`Matrix.mem_spectrum_iff_isRoot_charpoly`.
-/

open Complex Polynomial Matrix SimpleGraph

namespace Chem

/-- A primitive 12-th root of unity. -/
noncomputable def zeta12 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

/-- The Hückel (adjacency) eigenvalues of the cycle `C₁₂`. -/
noncomputable def huckelLevel (k : Fin 12) : ℝ := 2 * Real.cos (2 * Real.pi * k / 12)

/-- Adjacency matrix of the cycle graph `C₁₂`, over `ℂ`. -/
noncomputable def A12 : Matrix (Fin 12) (Fin 12) ℂ := (SimpleGraph.cycleGraph 12).adjMatrix ℂ

/-- The discrete Fourier (Vandermonde) matrix built from the powers of `ζ`. -/
noncomputable def P12 : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.of fun i k => zeta12 ^ (i.val * k.val)

/-- The diagonal matrix of Hückel levels. -/
noncomputable def D12 : Matrix (Fin 12) (Fin 12) ℂ :=
  Matrix.diagonal fun k => (huckelLevel k : ℂ)

theorem isPrimitiveRoot_zeta12 : IsPrimitiveRoot zeta12 12 := by
  have := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  simpa [zeta12] using this

theorem zeta12_pow_congr {a b : ℕ} (h : a % 12 = b % 12) : zeta12 ^ a = zeta12 ^ b := by
  have h1 : zeta12 ^ 12 = 1 := isPrimitiveRoot_zeta12.pow_eq_one
  have key : ∀ n : ℕ, zeta12 ^ n = zeta12 ^ (n % 12) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 12]
    rw [pow_add, pow_mul, h1, one_pow, one_mul]
  rw [key a, key b, h]

/-- `ζ^{-k} + ζ^{k} = 2 cos (2πk/12)`, written with the nonnegative exponent `11 k`. -/
theorem zeta12_pow_add_pow (m : ℕ) :
    zeta12 ^ (11 * m) + zeta12 ^ m = ((2 * Real.cos (2 * Real.pi * m / 12) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * m / 12 with ht
  have hw : zeta12 ^ m = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [zeta12, ← Complex.exp_nat_mul]
    congr 1
    push_cast [ht]
    ring
  have h1 : zeta12 ^ 12 = 1 := isPrimitiveRoot_zeta12.pow_eq_one
  have h12 : zeta12 ^ (11 * m) * zeta12 ^ m = 1 := by
    rw [← pow_add, show 11 * m + m = 12 * m by ring, pow_mul, h1, one_pow]
  have hinv : zeta12 ^ (11 * m) = Complex.exp (-(t : ℂ) * Complex.I) := by
    rw [eq_inv_of_mul_eq_one_left h12, hw, ← Complex.exp_neg, neg_mul]
  rw [hw, hinv, Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_ofNat,
    Complex.two_cos]
  ring

/-- The key diagonalisation identity: `A P = P D`. -/
theorem A12_mul_P12 : A12 * P12 = P12 * D12 := by
  have hadj : ∀ i j : Fin 12, (SimpleGraph.cycleGraph 12).Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
    decide
  have hne : ∀ i : Fin 12, (i : Fin 12) - 1 ≠ i + 1 := by decide
  have hplus : ∀ i : Fin 12, (i + 1).val % 12 = (i.val + 1) % 12 := by decide
  have hminus : ∀ i : Fin 12, (i - 1).val % 12 = (i.val + 11) % 12 := by decide
  ext i k
  rw [Matrix.mul_apply, D12, Matrix.mul_diagonal]
  have hstep : ∀ j : Fin 12, A12 i j * P12 j k
      = (if j = i - 1 then P12 j k else 0) + (if j = i + 1 then P12 j k else 0) := by
    intro j
    have hA : A12 i j = if (j = i - 1 ∨ j = i + 1) then 1 else 0 := by
      simp only [A12, SimpleGraph.adjMatrix_apply]
      exact if_congr (hadj i j) rfl rfl
    rw [hA]
    by_cases h1 : j = i - 1
    · simp [h1, hne i]
    · by_cases h2 : j = i + 1
      · simp [h2, (hne i).symm]
      · simp [h1, h2]
  rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have e1 : P12 (i - 1) k = P12 i k * zeta12 ^ (11 * k.val) := by
    show zeta12 ^ ((i - 1).val * k.val) = zeta12 ^ (i.val * k.val) * zeta12 ^ (11 * k.val)
    rw [← pow_add]
    exact zeta12_pow_congr (by
      have := Nat.ModEq.mul_right k.val (hminus i)
      simpa [Nat.ModEq, Nat.add_mul] using this)
  have e2 : P12 (i + 1) k = P12 i k * zeta12 ^ k.val := by
    show zeta12 ^ ((i + 1).val * k.val) = zeta12 ^ (i.val * k.val) * zeta12 ^ k.val
    rw [← pow_add]
    exact zeta12_pow_congr (by
      have := Nat.ModEq.mul_right k.val (hplus i)
      simpa [Nat.ModEq, Nat.add_mul] using this)
  rw [e1, e2, huckelLevel, ← mul_add, zeta12_pow_add_pow k.val]

theorem P12_eq_vandermonde : P12 = Matrix.vandermonde (fun i : Fin 12 => zeta12 ^ i.val) := by
  ext i j
  simp [P12, Matrix.vandermonde_apply, pow_mul]

theorem P12_isUnit : IsUnit P12 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, P12_eq_vandermonde,
    Ne, Matrix.det_vandermonde_eq_zero_iff]
  push_neg
  intro i j h
  exact Fin.ext (isPrimitiveRoot_zeta12.pow_inj i.isLt j.isLt h)

/-- The characteristic polynomial of the adjacency matrix of `C₁₂` splits with roots the
Hückel levels `2 cos (2πk/12)`, `k = 0, …, 11` (with multiplicity). -/
theorem charpoly_A12 : A12.charpoly = ∏ k : Fin 12, (X - C ((huckelLevel k : ℂ))) := by
  obtain ⟨U, hU⟩ := P12_isUnit
  have hmul : A12 * U.val = U.val * D12 := by rw [hU]; exact A12_mul_P12
  have hconj : A12 = U.val * D12 * (U⁻¹ : (Matrix (Fin 12) (Fin 12) ℂ)ˣ).val := by
    rw [← hmul, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [hconj, Matrix.charpoly_units_conj U D12, D12, Matrix.charpoly_diagonal]

/-- The Hückel molecular orbitals of `C₁₂`: the vector with coefficients `ζ^{jk}` is an
eigenvector of the adjacency matrix with eigenvalue `2 cos (2πk/12)`. -/
theorem huckel_C12_eigenvector (k : Fin 12) :
    A12.mulVec (fun j => zeta12 ^ (j.val * k.val))
      = (huckelLevel k : ℂ) • fun j => zeta12 ^ (j.val * k.val) := by
  funext i
  have h := congrFun (congrFun A12_mul_P12 i) k
  rw [Matrix.mul_apply, D12, Matrix.mul_diagonal] at h
  simpa [Matrix.mulVec, dotProduct, P12, mul_comm] using h

/-- **Hückel theory for the cycle `C₁₂`**: the eigenvalues of the adjacency matrix of the
cycle graph on 12 vertices are exactly the numbers `2 cos (2πk/12)`, `k = 0, …, 11`. -/
theorem huckel_C12 (mu : ℂ) :
    mu ∈ spectrum ℂ ((SimpleGraph.cycleGraph 12).adjMatrix ℂ) ↔
      ∃ k : Fin 12, mu = ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ) := by
  rw [show (SimpleGraph.cycleGraph 12).adjMatrix ℂ = A12 from rfl,
    Matrix.mem_spectrum_iff_isRoot_charpoly, charpoly_A12, Polynomial.IsRoot.def,
    Polynomial.eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [Finset.prod_eq_zero_iff]
  simp [sub_eq_zero, huckelLevel]

end Chem

