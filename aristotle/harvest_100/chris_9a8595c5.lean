/-
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 2707
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2707
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

/-- **Cos Trace Norm 2707.**

For the real `n × n` diagonal matrix `C f = diag (cos (f 0), …, cos (f (n-1)))` we record
three bounds:

* the trace norm (sum of the singular values, which for a diagonal matrix is the sum of the
  absolute values of the diagonal entries) is at most `n`;
* consequently `|trace (C f)| ≤ n`;
* a quadratic lower bound for the trace, `n - (1/2) * ∑ i, (f i)^2 ≤ trace (C f)`,
  coming from the elementary estimate `1 - x^2/2 ≤ cos x`.
-/
theorem CosTraceNorm2707 {n : ℕ} (f : Fin n → ℝ) :
    (∑ i : Fin n, |Matrix.diagonal (fun j : Fin n => Real.cos (f j)) i i| ≤ (n : ℝ)) ∧
    |Matrix.trace (Matrix.diagonal (fun j : Fin n => Real.cos (f j)))| ≤ (n : ℝ) ∧
    (n : ℝ) - (1 / 2) * ∑ i : Fin n, (f i) ^ 2 ≤
      Matrix.trace (Matrix.diagonal (fun j : Fin n => Real.cos (f j))) := by
  have hdiag : ∀ i : Fin n,
      Matrix.diagonal (fun j : Fin n => Real.cos (f j)) i i = Real.cos (f i) := by
    intro i; simp [Matrix.diagonal_apply_eq]
  have htrace : Matrix.trace (Matrix.diagonal (fun j : Fin n => Real.cos (f j)))
      = ∑ i : Fin n, Real.cos (f i) := by
    simp [Matrix.trace_diagonal]
  have habs : ∑ i : Fin n, |Matrix.diagonal (fun j : Fin n => Real.cos (f j)) i i| ≤ (n : ℝ) := by
    calc ∑ i : Fin n, |Matrix.diagonal (fun j : Fin n => Real.cos (f j)) i i|
        = ∑ i : Fin n, |Real.cos (f i)| := by
          exact Finset.sum_congr rfl fun i _ => by rw [hdiag i]
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Real.abs_cos_le_one (f i)
      _ = (n : ℝ) := by simp
  refine ⟨habs, ?_, ?_⟩
  · calc |Matrix.trace (Matrix.diagonal (fun j : Fin n => Real.cos (f j)))|
        = |∑ i : Fin n, Real.cos (f i)| := by rw [htrace]
      _ ≤ ∑ i : Fin n, |Real.cos (f i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (n : ℝ) := by
          refine le_trans (le_of_eq ?_) habs
          exact Finset.sum_congr rfl fun i _ => by rw [hdiag i]
  · rw [htrace]
    have hlb : ∀ i : Fin n, 1 - (f i) ^ 2 / 2 ≤ Real.cos (f i) := fun i =>
      Real.one_sub_sq_div_two_le_cos
    calc (n : ℝ) - (1 / 2) * ∑ i : Fin n, (f i) ^ 2
        = ∑ i : Fin n, (1 - (f i) ^ 2 / 2) := by
          rw [Finset.sum_sub_distrib]
          simp [Finset.mul_sum, div_eq_mul_inv, mul_comm]
      _ ≤ ∑ i : Fin n, Real.cos (f i) := Finset.sum_le_sum fun i _ => hlb i

end Brockian

