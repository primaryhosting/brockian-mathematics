/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Hückel theory for the cycle `C₇`

In Hückel molecular orbital theory the (reduced) Hamiltonian of a conjugated
cyclic polyene `Cₙ` is the adjacency matrix of the cycle graph `Cₙ`, and the
orbital energies are `α + β λ` where `λ` runs over the adjacency eigenvalues.
For `n = 7` (the cycloheptatrienyl system) the eigenvalues are
`2 cos (2πk/7)`, `k = 0, …, 6`.

The proof diagonalises the adjacency matrix by the discrete Fourier
(Vandermonde) matrix built from `ω = exp (2πi/7)`.
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The primitive 7-th root of unity `ω = exp (2πi/7)`. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

/-- The Hückel eigenvalues of the cycle `C₇`: `2 cos (2πk/7)` for `k = 0, …, 6`
(in units of the resonance integral `β`, relative to the Coulomb integral `α`). -/
noncomputable def huckelVal (k : Fin 7) : ℂ := (2 * Real.cos (2 * Real.pi * k / 7) : ℝ)

/-- The matrix of Hückel eigenvectors: the `7 × 7` discrete Fourier (Vandermonde)
matrix with entries `ω ^ (i * k)`. -/
noncomputable def V : Matrix (Fin 7) (Fin 7) ℂ :=
  Matrix.vandermonde (fun k : Fin 7 => om ^ (k : ℕ))

theorem om_primitive : IsPrimitiveRoot om 7 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 7 (by norm_num)

theorem om_pow_seven : om ^ 7 = 1 := om_primitive.pow_eq_one

theorem V_apply (i k : Fin 7) : V i k = (om ^ (k : ℕ)) ^ (i : ℕ) := by
  simp [V, Matrix.vandermonde_apply, ← pow_mul, Nat.mul_comm]

theorem om_pow_eq_exp (k : Fin 7) :
    om ^ (k : ℕ) = Complex.exp (((2 * Real.pi * k / 7 : ℝ) : ℂ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ω ^ k + ω ^ (6k) = 2 cos (2πk/7)`, the Hückel eigenvalue. -/
theorem om_add_inv (k : Fin 7) :
    om ^ (k : ℕ) + (om ^ (k : ℕ)) ^ 6 = huckelVal k := by
  set t : ℝ := 2 * Real.pi * k / 7 with ht
  rw [om_pow_eq_exp k, ← Complex.exp_nat_mul]
  have h7 : Complex.exp ((7 : ℕ) * ((t : ℂ) * Complex.I)) = 1 := by
    have h : ((7 : ℕ) : ℂ) * ((t : ℂ) * Complex.I)
        = ((k : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [ht]; push_cast; ring
    rw [h]
    exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℕ)
  have h6 : Complex.exp ((6 : ℕ) * ((t : ℂ) * Complex.I))
      = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have h : ((6 : ℕ) : ℂ) * ((t : ℂ) * Complex.I)
        = ((7 : ℕ) * ((t : ℂ) * Complex.I)) + (-((t : ℂ) * Complex.I)) := by
      push_cast; ring
    rw [h, Complex.exp_add, h7, one_mul]
  rw [h6, huckelVal, ht]
  push_cast
  rw [Complex.cos]
  ring_nf

theorem pow_mod_seven (z : ℂ) (h : z ^ 7 = 1) (a : ℕ) : z ^ (a % 7) = z ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 7]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

/-- The adjacency matrix of `C₇` is diagonalised by the Fourier matrix `V`. -/
theorem adj_mul_V : ((cycleGraph 7).adjMatrix ℂ) * V = V * Matrix.diagonal huckelVal := by
  ext i k
  have hne : (i - 1 : Fin 7) ≠ i + 1 := by revert i; decide
  have h1 : ((i + 1 : Fin 7) : ℕ) = ((i : ℕ) + 1) % 7 := by revert i; decide
  have h2 : ((i - 1 : Fin 7) : ℕ) = ((i : ℕ) + 6) % 7 := by revert i; decide
  have hz : (om ^ (k : ℕ)) ^ 7 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, om_pow_seven, one_pow]
  have hsum : (((cycleGraph 7).adjMatrix ℂ) * V) i k = V (i - 1) k + V (i + 1) k := by
    rw [Matrix.mul_apply, show (∑ j, ((cycleGraph 7).adjMatrix ℂ) i j * V j k) =
      ((cycleGraph 7).adjMatrix ℂ *ᵥ fun j => V j k) i from rfl,
      SimpleGraph.adjMatrix_mulVec_apply,
      show ((cycleGraph 7).neighborFinset i) = {i - 1, i + 1} from
        SimpleGraph.cycleGraph_neighborFinset, Finset.sum_pair hne]
  rw [hsum, Matrix.mul_diagonal, V_apply, V_apply, V_apply, h1, h2,
    pow_mod_seven _ hz, pow_mod_seven _ hz, ← om_add_inv k, pow_add, pow_add]
  ring

theorem V_det_ne_zero : V.det ≠ 0 := by
  rw [V, Matrix.det_vandermonde, Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  rw [Finset.mem_Ioi] at hj
  refine sub_ne_zero.mpr ?_
  intro hcon
  exact absurd (Fin.ext (om_primitive.pow_inj j.isLt i.isLt hcon)) (ne_of_gt hj)

/-- **Hückel theory for the cycle `C₇` (the cycloheptatrienyl system).**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₇`
factors as `∏ₖ (X - 2 cos (2πk/7))`, `k = 0, …, 6`; that is, the adjacency
eigenvalues of `C₇` are exactly the seven numbers `2 cos (2πk/7)`, counted with
multiplicity. -/
theorem huckel_C7 :
    ((cycleGraph 7).adjMatrix ℂ).charpoly =
      ∏ k : Fin 7, (X - C ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ)) := by
  have hU : IsUnit V.det := isUnit_iff_ne_zero.mpr V_det_ne_zero
  set U : (Matrix (Fin 7) (Fin 7) ℂ)ˣ := Matrix.nonsingInvUnit V hU
  have hUv : (U : Matrix (Fin 7) (Fin 7) ℂ) = V := rfl
  have hUi : ((U⁻¹ : (Matrix (Fin 7) (Fin 7) ℂ)ˣ) : Matrix (Fin 7) (Fin 7) ℂ) = V⁻¹ := rfl
  have key : ((cycleGraph 7).adjMatrix ℂ)
      = (U : Matrix (Fin 7) (Fin 7) ℂ) * Matrix.diagonal huckelVal
          * (U⁻¹ : (Matrix (Fin 7) (Fin 7) ℂ)ˣ) := by
    rw [hUv, hUi, ← adj_mul_V, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.mul_one]
  rw [key, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]
  rfl

/-- The explicit Hückel molecular orbitals of `C₇`: the vector
`j ↦ ω ^ (k j)` is an eigenvector of the adjacency matrix of `C₇` with
eigenvalue `2 cos (2πk/7)`. -/
theorem huckel_C7_eigenvector (k : Fin 7) :
    ((cycleGraph 7).adjMatrix ℂ) *ᵥ (fun j : Fin 7 => (om ^ (k : ℕ)) ^ (j : ℕ))
      = ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ) •
          (fun j : Fin 7 => (om ^ (k : ℕ)) ^ (j : ℕ)) := by
  funext i
  have h := congrFun (congrFun adj_mul_V i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal, V_apply] at h
  simpa [Matrix.mulVec, dotProduct, V_apply, huckelVal, mul_comm] using h

/-- The set of adjacency eigenvalues (roots of the characteristic polynomial) of
`C₇` is exactly `{2 cos (2πk/7) : k = 0, …, 6}`. -/
theorem huckel_C7_roots :
    {μ : ℂ | ((cycleGraph 7).adjMatrix ℂ).charpoly.IsRoot μ}
      = Set.range (fun k : Fin 7 => ((2 * Real.cos (2 * Real.pi * k / 7) : ℝ) : ℂ)) := by
  ext μ
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot, huckel_C7, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero, Set.mem_range]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩

end Chem

