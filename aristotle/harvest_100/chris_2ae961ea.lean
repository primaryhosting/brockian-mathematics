/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
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

/-- The "cosine trace" of the regular representation at angle `x`:
`∑_{k < n} cos (k * x)`. -/
noncomputable def cosTrace (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.cos (k * x)

/-- The full trace of the `1597`-th roots of unity vanishes:
`∑_{k < 1597} cos (2πk/1597) = 0`. -/
theorem cosTrace_root_of_unity_1597 :
    (∑ k ∈ Finset.range 1597, Real.cos (2 * Real.pi * k / 1597)) = 0 := by
  have h := (Complex.isPrimitiveRoot_exp 1597 (by norm_num)).geom_sum_eq_zero (by norm_num)
  have h2 := congrArg Complex.re h
  rw [Complex.re_sum, Complex.zero_re] at h2
  rw [← h2]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [← Complex.exp_nat_mul]
  have hk : (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / ((1597 : ℕ) : ℂ)) =
      ((2 * Real.pi * k / 1597 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hk, Complex.exp_ofReal_mul_I_re]

/-- The cosine trace is bounded in absolute value by the dimension. -/
theorem abs_cosTrace_le (n : ℕ) (x : ℝ) : |cosTrace n x| ≤ n := by
  calc |cosTrace n x| ≤ ∑ k ∈ Finset.range n, |Real.cos (k * x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => Real.abs_cos_le_one _
    _ = n := by simp

/-- The bound is attained at `x = 0`. -/
theorem cosTrace_zero (n : ℕ) : cosTrace n 0 = n := by
  simp [cosTrace]

/--
**Cos Trace Norm 1597.**

For the dimension `n = 1597`:

* the cosine trace `x ↦ ∑_{k < 1597} cos (k x)` is bounded in absolute value by `1597`;
* this bound is sharp, being attained at `x = 0`;
* at the primitive `1597`-th root of unity the trace vanishes:
  `∑_{k < 1597} cos (2πk/1597) = 0`.
-/
theorem CosTraceNorm1597 :
    (∀ x : ℝ, |cosTrace 1597 x| ≤ 1597) ∧
      cosTrace 1597 0 = 1597 ∧
      (∑ k ∈ Finset.range 1597, Real.cos (2 * Real.pi * k / 1597)) = 0 := by
  refine ⟨fun x => ?_, ?_, cosTrace_root_of_unity_1597⟩
  · simpa using abs_cosTrace_le 1597 x
  · simpa using cosTrace_zero 1597

end Brockian

