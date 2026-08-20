/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Zeta23Redux.LinAlg

/-- Abel summation / Hardy–Littlewood–Pólya: if `m` is decreasing on `range d` and the partial
sums of `f` are dominated by those of `g`, with equal total sums, then `∑ m f ≤ ∑ m g`. -/

lemma trace_mul_eq_conj_diag {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix.trace (A * B) = Matrix.trace (
      Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
        (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
          (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) *
      Matrix.diagonal (fun j => ((hB.eigenvalues j : ℝ) : ℂ)) *
      star (star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ))) := by
  set U : Matrix (Fin d) (Fin d) ℂ := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hU
  set V : Matrix (Fin d) (Fin d) ℂ := (hB.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) with hV
  set Dm : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) with hDm
  set Dn : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (fun i => ((hB.eigenvalues i : ℝ) : ℂ)) with hDn
  have hAeq : A = U * Dm * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hDm, hU]
    simp [Function.comp_def]
  have hBeq : B = V * Dn * star V := by
    conv_lhs => rw [hB.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hDn, hV]
    simp [Function.comp_def]
  rw [hAeq, hBeq, Matrix.star_mul, star_star]
  have h1 : U * Dm * star U * (V * Dn * star V) = U * (Dm * (star U * V) * Dn * star V) := by
    simp [mul_assoc]
  rw [h1, Matrix.trace_mul_comm, mul_assoc]

/-- **Von Neumann's trace inequality** for Hermitian matrices: if `mu` and `nu` list the
eigenvalues of the Hermitian matrices `A` and `B` in decreasing order, then
`Re (trace (A * B)) ≤ ∑ i, mu i * nu i`. -/
