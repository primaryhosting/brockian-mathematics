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

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file constructs an explicit sequence in `[0, 1)` whose empirical distribution is
asymptotically the uniform one: for every subinterval `[a, b) ⊆ [0, 1)` the proportion of
the first `N` terms lying in `[a, b)` converges to `b - a`.

The construction is the "triangular block" sequence
`0/1 ; 0/2, 1/2 ; 0/3, 1/3, 2/3 ; 0/4, …` .
-/

open Filter Topology

namespace Brockian.Equidistribution

/-- Triangular numbers: `tri k = 0 + 1 + ⋯ + k`. -/

lemma exists_block_index (N : ℕ) :
    ∃ K : ℕ, tri K ≤ N ∧ N ≤ tri (K + 1) ∧ (K : ℝ) ≤ Real.sqrt (2 * N) := by
  refine ⟨idx N, tri_idx_le N, le_of_lt (lt_tri_idx_succ N), ?_⟩
  have h : idx N * idx N ≤ 2 * N := by
    have h1 : tri (idx N) ≤ N := tri_idx_le N
    have h2 : 2 * tri (idx N) = idx N * (idx N + 1) := two_mul_tri _
    nlinarith
  have hR : ((idx N : ℝ)) * (idx N : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast h
  have hs : Real.sqrt ((idx N : ℝ) * (idx N : ℝ)) ≤ Real.sqrt (2 * N) := Real.sqrt_le_sqrt hR
  rwa [Real.sqrt_mul_self (Nat.cast_nonneg (idx N))] at hs

/-- The error bound function. -/
