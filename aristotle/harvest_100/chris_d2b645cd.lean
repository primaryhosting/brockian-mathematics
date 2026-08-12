import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Brockian

open Matrix

/-- The trace norm (Schatten `1`-norm) of a Hermitian complex matrix: the sum of the absolute
values of its eigenvalues.  (It is set to `0` on non-Hermitian matrices, which we never use.) -/
noncomputable def hermTraceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ℝ :=
  if h : A.IsHermitian then ∑ i, |h.eigenvalues i| else 0

/-- The `N × N` cosine kernel matrix attached to frequencies `w`, weights `c` and nodes `x`:
its `(i, j)` entry is `∑ k, c k * cos (w k * (x i - x j))`. -/
noncomputable def cosKernel {N m : ℕ} (c w : Fin m → ℝ) (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ((∑ k, c k * Real.cos (w k * (x i - x j)) : ℝ) : ℂ)

/-- A rectangular factor `B` with `Bᴴ * B = cosKernel c w x` (for nonnegative weights). -/
noncomputable def cosFactor {N m : ℕ} (c w : Fin m → ℝ) (x : Fin N → ℝ) :
    Matrix (Fin m × Fin 2) (Fin N) ℂ :=
  fun p j => ((Real.sqrt (c p.1) *
    (if p.2 = 0 then Real.cos (w p.1 * x j) else Real.sin (w p.1 * x j)) : ℝ) : ℂ)

theorem cosKernel_eq_conjTranspose_mul {N m : ℕ} {c w : Fin m → ℝ} (hc : ∀ k, 0 ≤ c k)
    (x : Fin N → ℝ) :
    cosKernel c w x = (cosFactor c w x)ᴴ * cosFactor c w x := by
  ext i j
  simp only [cosKernel, Matrix.mul_apply, Matrix.conjTranspose_apply, cosFactor, RCLike.star_def,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  norm_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hsq : Real.sqrt (c k) * Real.sqrt (c k) = c k := Real.mul_self_sqrt (hc k)
  simp only [Fin.sum_univ_two, mul_sub]
  norm_num [Real.cos_sub]
  linear_combination (Real.cos (w k * x i) * Real.cos (w k * x j)
    + Real.sin (w k * x i) * Real.sin (w k * x j)) * hsq.symm

theorem cosKernel_posSemidef {N m : ℕ} {c w : Fin m → ℝ} (hc : ∀ k, 0 ≤ c k) (x : Fin N → ℝ) :
    (cosKernel c w x).PosSemidef := by
  rw [cosKernel_eq_conjTranspose_mul hc x]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem cosKernel_isHermitian {N m : ℕ} {c w : Fin m → ℝ} (hc : ∀ k, 0 ≤ c k) (x : Fin N → ℝ) :
    (cosKernel c w x).IsHermitian :=
  (cosKernel_posSemidef hc x).isHermitian

theorem cosKernel_trace {N m : ℕ} (c w : Fin m → ℝ) (x : Fin N → ℝ) :
    (cosKernel c w x).trace = ((N : ℂ) * ((∑ k, c k : ℝ) : ℂ)) := by
  simp [Matrix.trace, Matrix.diag, cosKernel, Finset.sum_const, nsmul_eq_mul]

/-- **Trace-norm bound for cosine kernel matrices.**
For nonnegative weights `c k`, arbitrary frequencies `w k` and arbitrary nodes `x i`, the
`N × N` matrix with entries `∑ k, c k * cos (w k * (x i - x j))` has trace norm exactly
`N * ∑ k, c k`; in particular this is a sharp upper bound. -/
theorem CosTraceNorm3499 {N m : ℕ} {c w : Fin m → ℝ} (hc : ∀ k, 0 ≤ c k) (x : Fin N → ℝ) :
    hermTraceNorm (cosKernel c w x) = (N : ℝ) * ∑ k, c k := by
  have hH : (cosKernel c w x).IsHermitian := cosKernel_isHermitian hc x
  have hPSD : (cosKernel c w x).PosSemidef := cosKernel_posSemidef hc x
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hPSD.eigenvalues_nonneg i
  have htr := (hH.trace_eq_sum_eigenvalues (𝕜 := ℂ)).symm.trans (cosKernel_trace c w x)
  have htr' : (∑ i, hH.eigenvalues i) = (N : ℝ) * ∑ k, c k := by
    simpa using congrArg Complex.re htr
  rw [hermTraceNorm, dif_pos hH, Finset.sum_congr rfl (fun i _ => abs_of_nonneg (hnn i))]
  exact htr'

/-- Sharpness restated as an upper bound. -/
theorem cosKernel_hermTraceNorm_le {N m : ℕ} {c w : Fin m → ℝ} (hc : ∀ k, 0 ≤ c k)
    (x : Fin N → ℝ) :
    hermTraceNorm (cosKernel c w x) ≤ (N : ℝ) * ∑ k, c k :=
  le_of_eq (CosTraceNorm3499 hc x)

/-- The plain cosine matrix `[cos (x i - x j)]` has trace norm exactly `N`. -/
theorem cosMatrix_hermTraceNorm {N : ℕ} (x : Fin N → ℝ) :
    hermTraceNorm (cosKernel (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) x)
      = (N : ℝ) := by
  simpa using CosTraceNorm3499 (fun _ : Fin 1 => zero_le_one) x

end Brockian

