import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

/-- Every diagonal entry of a matrix `U` with `U * Uᴴ = 1` has norm at most `1`:
the `i`-th row of `U` is a unit vector. -/

theorem CosTraceNorm4001_card {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (hU : U * Uᴴ = 1) (θ : n → ℝ) :
    ‖(U * Matrix.diagonal fun i => (Real.cos (θ i) : ℂ)).trace‖
      ≤ (Fintype.card n : ℝ) := by
  refine le_trans (CosTraceNorm4001 U hU θ) ?_
  have : ∑ _i : n, (1 : ℝ) = (Fintype.card n : ℝ) := by
    simp [Finset.card_univ]
  rw [← this]
  exact Finset.sum_le_sum fun i _ => Real.abs_cos_le_one (θ i)

/-- Sanity check: the hypothesis of `CosTraceNorm4001` is satisfiable (the identity matrix). -/
example {n : Type*} [Fintype n] [DecidableEq n] :
    (1 : Matrix n n ℂ) * (1 : Matrix n n ℂ)ᴴ = 1 := by
  simp

end Brockian

