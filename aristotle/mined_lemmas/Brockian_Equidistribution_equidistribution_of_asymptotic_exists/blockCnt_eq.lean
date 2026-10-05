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

lemma blockCnt_eq (m : ℕ) (hm : 0 < m) (hb : b ≤ 1) :
    blockCnt a b m = ⌈b * m⌉₊ - ⌈a * m⌉₊ := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hceil_le : ⌈b * m⌉₊ ≤ m := by
    have hbm : b * m ≤ (m : ℝ) := by nlinarith
    exact Nat.ceil_le.2 (by exact_mod_cast hbm)
  have hset : ((Finset.range m).filter (fun j : ℕ => ((j : ℝ) / (m : ℝ)) ∈ Set.Ico a b))
      = Finset.Ico ⌈a * m⌉₊ ⌈b * m⌉₊ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Set.mem_Ico]
    constructor
    · rintro ⟨hj, hja, hjb⟩
      refine ⟨Nat.ceil_le.2 ?_, Nat.lt_ceil.2 ?_⟩
      · rw [le_div_iff₀ hmR] at hja; linarith
      · rw [div_lt_iff₀ hmR] at hjb; linarith
    · rintro ⟨hja, hjb⟩
      have hja' : a * m ≤ (j : ℝ) := by
        have hc : ((⌈a * m⌉₊ : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hja
        linarith [Nat.le_ceil (a * m)]
      have hjb' : (j : ℝ) < b * m := Nat.lt_ceil.1 hjb
      refine ⟨by omega, ?_, ?_⟩
      · rw [le_div_iff₀ hmR]; linarith
      · rw [div_lt_iff₀ hmR]; linarith
  rw [blockCnt, hset, Nat.card_Ico]

