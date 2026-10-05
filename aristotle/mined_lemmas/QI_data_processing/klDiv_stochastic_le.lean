import Mathlib
import RequestProject.Classical

/-!
# Quantum relative entropy

Definitions of the matrix logarithm (via the continuous functional calculus), the Umegaki
relative entropy of two density matrices, and quantum channels in Kraus form.
-/

open Matrix Unitary
open scoped BigOperators ComplexOrder

namespace QI

variable {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [Fintype ι]

/-- The matrix logarithm of a Hermitian matrix, defined through the continuous functional
calculus (with the convention `log 0 = 0`, so that vanishing eigenvalues contribute nothing). -/

theorem klDiv_stochastic_le [Fintype ι] [Fintype κ] (S : κ → ι → ℝ)
    (hS : ∀ k i, 0 ≤ S k i) (hcol : ∀ i, ∑ k, S k i = 1)
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    klDiv (fun k => ∑ i, S k i * p i) (fun k => ∑ i, S k i * q i) ≤ klDiv p q := by
  have step : ∀ k : κ,
      (∑ i, S k i * p i) * (Real.log (∑ i, S k i * p i) - Real.log (∑ i, S k i * q i))
        ≤ ∑ i, S k i * (p i * (Real.log (p i) - Real.log (q i))) := by
    intro k
    have h := log_sum_le (fun i => S k i * p i) (fun i => S k i * q i)
      (fun i => mul_nonneg (hS k i) (hp i)) (fun i => mul_nonneg (hS k i) (le_of_lt (hq i)))
      (fun i hi => by
        rcases mul_eq_zero.1 hi with h0 | h0
        · simp [h0]
        · exact absurd h0 (ne_of_gt (hq i)))
    refine h.trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases eq_or_lt_of_le (hS k i) with h0 | h0
    · simp [← h0]
    · rcases eq_or_lt_of_le (hp i) with hp0 | hp0
      · simp [← hp0]
      · rw [Real.log_mul (ne_of_gt h0) (ne_of_gt hp0),
          Real.log_mul (ne_of_gt h0) (ne_of_gt (hq i))]
        ring
  calc klDiv (fun k => ∑ i, S k i * p i) (fun k => ∑ i, S k i * q i)
      ≤ ∑ k, ∑ i, S k i * (p i * (Real.log (p i) - Real.log (q i))) :=
        Finset.sum_le_sum fun k _ => step k
    _ = klDiv p q := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, hcol i, one_mul]

end QI

import Mathlib

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

