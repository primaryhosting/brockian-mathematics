import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
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

/-!
Key Mathlib ingredients used below:
* `Matrix.IsHermitian.trace_eq_sum_eigenvalues` — the trace of a Hermitian matrix is the sum
  of its eigenvalues;
* `Matrix.posSemidef_conjTranspose_mul_self` — Gram matrices `Bᴴ * B` are positive semidefinite;
* `Matrix.PosSemidef.eigenvalues_nonneg` — eigenvalues of a PSD matrix are nonnegative.
-/

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (nuclear norm, Schatten 1-norm) of a Hermitian real matrix:
the sum of the absolute values of its eigenvalues. -/

noncomputable def hermTraceNorm {A : Matrix n n ℝ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The trace norm dominates the absolute value of the trace. -/

theorem hermTraceNorm_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    hermTraceNorm hA.isHermitian = A.trace := by
  rw [hermTraceNorm, hA.isHermitian.trace_eq_sum_eigenvalues]
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hA.eigenvalues_nonneg i)

/-- The amplitude-weighted cosine kernel matrix `K i j = a i * a j * cos (x i - x j)`. -/

noncomputable def cosKernelAmp (a x : n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => a i * a j * Real.cos (x i - x j)

/-- The cosine kernel matrix `C i j = cos (x i - x j)`. -/

noncomputable def cosKernel (x : n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => Real.cos (x i - x j)

omit [Fintype n] [DecidableEq n] in

theorem cosKernelAmp_one (x : n → ℝ) : cosKernelAmp (fun _ => (1 : ℝ)) x = cosKernel x := by
  ext i j
  simp [cosKernelAmp, cosKernel]

omit [Fintype n] [DecidableEq n] in
/-- The weighted cosine kernel is the Gram matrix of the planar vectors
`a i • (cos (x i), sin (x i))`. -/

theorem cosKernelAmp_eq_gram (a x : n → ℝ) :
    cosKernelAmp a x =
      (Matrix.of fun (k : Fin 2) (i : n) => ![a i * Real.cos (x i), a i * Real.sin (x i)] k)ᴴ *
      (Matrix.of fun (k : Fin 2) (i : n) => ![a i * Real.cos (x i), a i * Real.sin (x i)] k) := by
  ext i j
  simp only [cosKernelAmp, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, star_trivial, Real.cos_sub, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

omit [DecidableEq n] in

theorem cosKernelAmp_posSemidef (a x : n → ℝ) : (cosKernelAmp a x).PosSemidef := by
  rw [cosKernelAmp_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq n] in

theorem cosKernel_posSemidef (x : n → ℝ) : (cosKernel x).PosSemidef := by
  rw [← cosKernelAmp_one x]
  exact cosKernelAmp_posSemidef _ x

omit [DecidableEq n] in

theorem trace_cosKernel (x : n → ℝ) : (cosKernel x).trace = Fintype.card n := by
  simp [Matrix.trace, Matrix.diag, cosKernel, Finset.card_univ]

/-- **Cos Trace Norm 2003.**
The trace norm (sum of the absolute values of the eigenvalues) of the cosine kernel matrix
`C i j = cos (x i - x j)` equals the cardinality of the index set, for arbitrary real
phases `x`.  Indeed `C` is the Gram matrix of the unit vectors `(cos xᵢ, sin xᵢ)`, hence
positive semidefinite, so its trace norm is its trace `∑ i, cos 0 = card n`. -/

theorem CosTraceNorm2003 (x : n → ℝ) :
    hermTraceNorm (cosKernel_posSemidef x).isHermitian = Fintype.card n := by
  rw [hermTraceNorm_of_posSemidef (cosKernel_posSemidef x), trace_cosKernel]

/-- Weighted extension of the family: the trace norm of the amplitude-weighted cosine
kernel `K i j = a i * a j * cos (x i - x j)` equals `∑ i, (a i)²`. -/
