import Mathlib

/-!
# Quantum relative entropy and data processing

This file develops, for finite-dimensional systems (complex matrices), the basic theory of the
Umegaki quantum relative entropy

`D(ρ‖σ) = Tr(ρ log ρ) - Tr(ρ log σ)`

for faithful (positive definite) density matrices, together with

* Klein's inequality `QI.relEntropy_nonneg` : `0 ≤ D(ρ‖σ)`;
* invariance under unitary channels `QI.relEntropy_unitary_conj`;
* the data-processing inequality `QI.data_processing_condExp` for trace-self-adjoint maps fixing `σ`
  (conditional expectations), and its concrete instance for the completely dephasing channel
  `QI.data_processing_dephasing`.
-/

open Matrix
open scoped ComplexOrder

namespace QI

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The logarithm of a (Hermitian) matrix, defined through the continuous functional calculus. -/

theorem trace_mul_sylvAux_re {t : ℝ} {U V : Matrix n n ℂ} (hU : star U * U = 1)
    (hV : star V * V = 1) {p q : n → ℝ} {P Q : Matrix n n ℂ}
    (hPd : P = U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * star U)
    (hQd : Q = V * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V) :
    (Matrix.trace ((P - Q)ᴴ * sylvAux t U V p q (P - Q))).re
      = ∑ j, ∑ k, (p j - q k) ^ 2 / (t * p j + q k) * Complex.normSq ((star U * V) j k) := by
  set C := star U * (P - Q) * V with hC
  set M : Matrix n n ℂ := Matrix.of (fun j k => C j k / ((t * p j + q k : ℝ) : ℂ)) with hM
  have hWdef : sylvAux t U V p q (P - Q) = U * M * star V := rfl
  have hCeq : C = Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * (star U * V)
      - (star U * V) * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) := by
    rw [hC, hPd, hQd]
    calc star U * (U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * star U
            - V * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V) * V
        = (star U * U) * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * (star U * V)
          - (star U * V) * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * (star V * V) := by
          noncomm_ring
      _ = _ := by rw [hU, hV, one_mul, mul_one]
  have hCentry : ∀ j k, C j k = ((p j - q k : ℝ) : ℂ) * (star U * V) j k := by
    intro j k
    rw [hCeq]
    simp [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have htr : Matrix.trace ((P - Q)ᴴ * (U * M * star V)) = Matrix.trace (Cᴴ * M) := by
    have h1 : Cᴴ = star V * (P - Q)ᴴ * U := by
      rw [hC]
      simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
    rw [h1]
    calc Matrix.trace ((P - Q)ᴴ * (U * M * star V))
        = Matrix.trace (star V * ((P - Q)ᴴ * (U * M))) := by
          rw [← Matrix.mul_assoc ((P - Q)ᴴ) (U * M) (star V), Matrix.trace_mul_comm]
      _ = Matrix.trace (star V * (P - Q)ᴴ * U * M) := by simp only [Matrix.mul_assoc]
  have hval : Matrix.trace (Cᴴ * M)
      = ((∑ k, ∑ j, (p j - q k) ^ 2 / (t * p j + q k)
          * Complex.normSq ((star U * V) j k) : ℝ) : ℂ) := by
    rw [Matrix.trace, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply, hM]
    simp only [Matrix.of_apply]
    rw [hCentry j k]
    exact aux_entry _ _ _
  rw [hWdef, htr, hval, Complex.ofReal_re, Finset.sum_comm]

/-- The solution of the Sylvester equation `t • (P * W) + W * Q = P - Q`, written in the
eigenbases of `P` and `Q`. -/
