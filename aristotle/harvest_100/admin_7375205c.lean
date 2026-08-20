import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The trace norm (sum of the absolute values of the eigenvalues) of the real diagonal
matrix `diagonal (fun i => cos (θ i))`. -/
noncomputable def cosTraceNorm {n : ℕ} (θ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |Real.cos (θ i)|

/-- The trace norm dominates the absolute value of the trace. -/
theorem abs_trace_le_cosTraceNorm {n : ℕ} (θ : Fin n → ℝ) :
    |Matrix.trace (Matrix.diagonal fun i : Fin n => Real.cos (θ i))| ≤ cosTraceNorm θ := by
  simp only [Matrix.trace_diagonal, cosTraceNorm]
  exact Finset.abs_sum_le_sum_abs _ _

/-- The trace norm is bounded by the dimension, since `|cos| ≤ 1`. -/
theorem cosTraceNorm_le_card {n : ℕ} (θ : Fin n → ℝ) : cosTraceNorm θ ≤ (n : ℝ) := by
  have h : ∀ i ∈ Finset.univ, |Real.cos (θ i)| ≤ (1 : ℝ) := fun i _ =>
    Real.abs_cos_le_one (θ i)
  calc cosTraceNorm θ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum h
    _ = (n : ℝ) := by simp

/-- The bound is attained exactly when every angle is a multiple of `π`, i.e. `sin (θ i) = 0`. -/
theorem cosTraceNorm_eq_card_iff {n : ℕ} (θ : Fin n → ℝ) :
    cosTraceNorm θ = (n : ℝ) ↔ ∀ i : Fin n, Real.sin (θ i) = 0 := by
  have habs : ∀ i : Fin n, |Real.cos (θ i)| = 1 ↔ Real.sin (θ i) = 0 := by
    intro i
    constructor
    · intro h
      have hc : Real.cos (θ i) ^ 2 = 1 := by
        have := congrArg (fun x : ℝ => x ^ 2) h
        simpa [sq_abs] using this
      have := Real.sin_sq_add_cos_sq (θ i)
      have hs : Real.sin (θ i) ^ 2 = 0 := by nlinarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
    · intro h
      have hpy := Real.sin_sq_add_cos_sq (θ i)
      rw [h] at hpy
      have hc : Real.cos (θ i) ^ 2 = 1 := by nlinarith
      have hsq : |Real.cos (θ i)| ^ 2 = 1 := by simpa [sq_abs] using hc
      nlinarith [abs_nonneg (Real.cos (θ i))]
  constructor
  · intro h i
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin n)), |Real.cos (θ j)| ≤ (1 : ℝ) :=
      fun j _ => Real.abs_cos_le_one (θ j)
    have hsum : ∑ j : Fin n, |Real.cos (θ j)| = ∑ _j : Fin n, (1 : ℝ) := by
      simpa [cosTraceNorm] using h
    have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum i (Finset.mem_univ i)
    exact (habs i).mp this
  · intro h
    have : ∀ i : Fin n, |Real.cos (θ i)| = 1 := fun i => (habs i).mpr (h i)
    simp [cosTraceNorm, this]

/-- **Cos Trace Norm 1279.** For the real diagonal matrix with entries `cos (θ i)`:
the absolute value of its trace is at most its trace norm, the trace norm is at most the
dimension `n`, and equality with `n` holds exactly when every `sin (θ i) = 0`. -/
theorem CosTraceNorm1279 {n : ℕ} (θ : Fin n → ℝ) :
    |Matrix.trace (Matrix.diagonal fun i : Fin n => Real.cos (θ i))| ≤ cosTraceNorm θ ∧
      cosTraceNorm θ ≤ (n : ℝ) ∧
      (cosTraceNorm θ = (n : ℝ) ↔ ∀ i : Fin n, Real.sin (θ i) = 0) :=
  ⟨abs_trace_le_cosTraceNorm θ, cosTraceNorm_le_card θ, cosTraceNorm_eq_card_iff θ⟩

end Brockian

