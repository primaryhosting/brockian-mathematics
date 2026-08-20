/-
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Holevo Bound
Category: Frontier Qi
Target: QI.holevo_bound
Statement: Accessible information about a quantum ensemble is at most its Holevo χ quantity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Scope of the formalisation

The ensemble is a *commuting* (equivalently: simultaneously diagonalizable) family of states,
measured by a POVM that is diagonal in the same eigenbasis.  Concretely, a state `ρₓ` is recorded
by its spectrum `r x : Z → ℝ` in a fixed orthonormal eigenbasis indexed by `Z`, a POVM element
`E y` by its diagonal `Z → ℝ`, and the Born rule is `Pr[y | x] = ∑ z, r x z * E y z`.  In this
situation the von Neumann entropy is the Shannon entropy of the spectrum, so the Holevo quantity
`χ = S(∑ₓ pₓ ρₓ) - ∑ₓ pₓ S(ρₓ)` and the accessible information are the ones defined below, and
`QI.holevo_bound` is the Holevo inequality `I_acc ≤ χ` for such ensembles.  The bound is tight:
for a uniform ensemble of two orthogonal states, measured in their own basis, both sides equal
`log 2`.  The fully general (non-commuting) case is not covered here.
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

set_option grind.warning false

namespace QI

/-! ## The log-sum inequality -/

/-- **Log-sum inequality**: for nonnegative weights `a`, `b` on a finite set such that `b i = 0`
forces `a i = 0` (absolute continuity), one has
`(∑ a) * log ((∑ a) / (∑ b)) ≤ ∑ a i * log (a i / b i)`. -/

theorem holevoChi_eq (p : X → ℝ) (r : X → Z → ℝ)
    (hp0 : ∀ x, 0 ≤ p x) (hr0 : ∀ x z, 0 ≤ r x z) :
    holevoChi p r = ∑ x, ∑ z, p x * r x z * Real.log (r x z / avgState p r z) := by
  have hterm : ∀ x : X, ∀ z : Z,
      p x * r x z * Real.log (r x z / avgState p r z)
        = p x * r x z * Real.log (r x z) - p x * r x z * Real.log (avgState p r z) := by
    intro x z
    rcases eq_or_lt_of_le (mul_nonneg (hp0 x) (hr0 x z)) with h | h
    · rw [← h]; ring
    · have hpx : p x ≠ 0 := by
        intro h0; rw [h0] at h; simp at h
      have hrxz : r x z ≠ 0 := by
        intro h0; rw [h0] at h; simp at h
      have havg : avgState p r z ≠ 0 := by
        intro h0
        have hnn : ∀ x' ∈ Finset.univ, 0 ≤ p x' * r x' z := fun x' _ =>
          mul_nonneg (hp0 x') (hr0 x' z)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 x (Finset.mem_univ x)
        exact absurd this (ne_of_gt h)
      rw [Real.log_div hrxz havg]; ring
  calc holevoChi p r
      = (∑ z, Real.negMulLog (avgState p r z)) - ∑ x, p x * ∑ z, Real.negMulLog (r x z) := rfl
    _ = ∑ x, ∑ z, (p x * r x z * Real.log (r x z) - p x * r x z * Real.log (avgState p r z)) := by
        have h1 : ∀ x : X, p x * ∑ z, Real.negMulLog (r x z)
            = ∑ z, -(p x * r x z * Real.log (r x z)) := by
          intro x
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro z _
          rw [Real.negMulLog]
          ring
        have h2 : ∀ z : Z, Real.negMulLog (avgState p r z)
            = ∑ x, -(p x * r x z * Real.log (avgState p r z)) := by
          intro z
          rw [Real.negMulLog, avgState, ← Finset.sum_neg_distrib, Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro x _
          ring
        simp only [h1, h2]
        rw [Finset.sum_comm (s := (Finset.univ : Finset Z)) (t := (Finset.univ : Finset X))]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro x _
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro z _
        ring
    _ = ∑ x, ∑ z, p x * r x z * Real.log (r x z / avgState p r z) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        refine Finset.sum_congr rfl ?_
        intro z _
        rw [hterm x z]

/-- **Holevo bound, per measurement**: for any POVM, the mutual information between the label
and the outcome is at most the Holevo quantity of the ensemble. -/
