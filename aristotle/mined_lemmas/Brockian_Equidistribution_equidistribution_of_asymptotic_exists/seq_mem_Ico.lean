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

lemma seq_mem_Ico (n : ℕ) : seq n ∈ Set.Ico (0 : ℝ) 1 := by
  have h1 : tri (idx n) ≤ n := tri_idx_le n
  have h2 : n < tri (idx n) + (idx n + 1) := by
    have := lt_tri_idx_succ n; rw [tri_succ] at this; omega
  have hpos : (0 : ℝ) < (idx n : ℝ) + 1 := by positivity
  constructor
  · exact div_nonneg (by positivity) (le_of_lt hpos)
  · rw [seq, div_lt_one hpos]
    have hlt : (n - tri (idx n) : ℕ) < idx n + 1 := by omega
    exact_mod_cast hlt

