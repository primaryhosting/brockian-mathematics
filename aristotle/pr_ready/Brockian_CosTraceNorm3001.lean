/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Finset Matrix

/-- The trace norm (Schatten 1-norm) of a real symmetric matrix: the sum of the absolute
values of its eigenvalues, which for a symmetric matrix coincides with the sum of its
singular values. -/
noncomputable def hermitianTraceNorm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The trace of a real symmetric matrix is the sum of its eigenvalues. -/
theorem trace_eq_sum_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : A.trace = ∑ i, hA.eigenvalues i := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut]
  show ((Unitary.toUnits hA.eigenvectorUnitary : (Matrix (Fin n) (Fin n) ℝ)ˣ) *
      diagonal hA.eigenvalues *
      ((Unitary.toUnits hA.eigenvectorUnitary)⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ)).trace = _
  rw [Matrix.trace_units_conj, Matrix.trace_diagonal]

/-- **Cos Trace Norm 3001.**
For the real diagonal matrix `D = diagonal (fun i => cos (θ i))` of size `n`, the absolute
value of its trace is bounded by its trace norm (the sum of its singular values, which for a
real diagonal matrix is `∑ i, |cos (θ i)|`), and that trace norm is in turn bounded by `n`.

The two steps are closed by `Finset.abs_sum_le_sum_abs` (the triangle inequality for finite
sums) and `Real.abs_cos_le_one`. -/
theorem CosTraceNorm3001 (n : ℕ) (θ : Fin n → ℝ) :
    |(Matrix.diagonal fun i => Real.cos (θ i)).trace| ≤ ∑ i, |Real.cos (θ i)| ∧
      ∑ i, |Real.cos (θ i)| ≤ (n : ℝ) := by
  constructor
  · rw [Matrix.trace_diagonal]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc ∑ i, |Real.cos (θ i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)
    _ = (n : ℝ) := by simp

/-- **Cos Trace Norm 3001, symmetric-matrix form.**
If a real symmetric `n × n` matrix `A` has eigenvalues of the form `cos (θ i)`, then
`|trace A|` is bounded by the trace norm of `A`, and that trace norm is at most `n`. -/
theorem CosTraceNorm3001_hermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (θ : Fin n → ℝ) (hev : ∀ i, hA.eigenvalues i = Real.cos (θ i)) :
    |A.trace| ≤ hermitianTraceNorm hA ∧ hermitianTraceNorm hA ≤ (n : ℝ) := by
  constructor
  · rw [trace_eq_sum_eigenvalues hA]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc hermitianTraceNorm hA ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => by
          rw [hev i]; exact Real.abs_cos_le_one (θ i)
    _ = (n : ℝ) := by simp

end Brockian


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

