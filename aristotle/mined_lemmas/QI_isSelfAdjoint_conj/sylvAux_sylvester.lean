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

theorem sylvAux_sylvester {t : ℝ} (ht : 0 < t) {U V : Matrix n n ℂ} (hU : star U * U = 1)
    (hUU : U * star U = 1) (hV : star V * V = 1) (hVV : V * star V = 1) {p q : n → ℝ}
    (hp : ∀ j, 0 < p j) (hq : ∀ k, 0 < q k) {P Q : Matrix n n ℂ}
    (hPd : P = U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * star U)
    (hQd : Q = V * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V) :
    (t : ℂ) • (P * sylvAux t U V p q (P - Q)) + sylvAux t U V p q (P - Q) * Q = P - Q := by
  set C := star U * (P - Q) * V with hC
  set M : Matrix n n ℂ := Matrix.of (fun j k => C j k / ((t * p j + q k : ℝ) : ℂ)) with hM
  have hdiag : (t : ℂ) • (Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * M)
      + M * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) = C := by
    ext j k
    have hpos : (0 : ℝ) < t * p j + q k := by
      have h1 : 0 < t * p j := mul_pos ht (hp j)
      have h2 := hq k
      linarith
    have hne : ((t * p j + q k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      hM, Matrix.of_apply, smul_eq_mul]
    field_simp
    push_cast
    ring
  calc (t : ℂ) • (P * (U * M * star V)) + (U * M * star V) * Q
      = U * ((t : ℂ) • (Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * M)
          + M * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ))) * star V := by
        rw [hPd, hQd, Matrix.mul_add, Matrix.add_mul]
        congr 1
        · rw [Matrix.mul_smul, Matrix.smul_mul]
          congr 1
          calc U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * star U * (U * M * star V)
              = U * Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * (star U * U) * M * star V := by
                noncomm_ring
            _ = U * (Matrix.diagonal (fun j => ((p j : ℝ) : ℂ)) * M) * star V := by
                rw [hU]; noncomm_ring
        · calc U * M * star V * (V * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V)
              = U * M * (star V * V) * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ)) * star V := by
                noncomm_ring
            _ = U * (M * Matrix.diagonal (fun k => ((q k : ℝ) : ℂ))) * star V := by
                rw [hV]; noncomm_ring
    _ = U * C * star V := by rw [hdiag]
    _ = P - Q := by
        rw [hC]
        calc U * (star U * (P - Q) * V) * star V
            = (U * star U) * (P - Q) * (V * star V) := by noncomm_ring
          _ = P - Q := by rw [hUU, hVV, one_mul, mul_one]

