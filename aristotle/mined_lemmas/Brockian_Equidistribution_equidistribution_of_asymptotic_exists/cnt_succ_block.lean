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

lemma cnt_succ_block (k : ℕ) :
    cnt a b (tri (k + 1)) = cnt a b (tri k) + blockCnt a b (k + 1) := by
  have hsplit : Finset.range (tri (k + 1))
      = Finset.range (tri k) ∪ Finset.Ico (tri k) (tri (k + 1)) := by
    rw [Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt (tri_lt_tri_succ k))]
  have hdisj : Disjoint ((Finset.range (tri k)).filter (fun n => seq n ∈ Set.Ico a b))
      ((Finset.Ico (tri k) (tri (k + 1))).filter (fun n => seq n ∈ Set.Ico a b)) := by
    apply Finset.disjoint_filter_filter
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 (tri k) (tri (k + 1))
  have hcard : ((Finset.Ico (tri k) (tri (k + 1))).filter
      (fun n => seq n ∈ Set.Ico a b)).card = blockCnt a b (k + 1) := by
    rw [blockCnt]
    apply Finset.card_bij' (fun n _ => n - tri k) (fun j _ => j + tri k)
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      obtain ⟨⟨h1, h2⟩, h3⟩ := hn
      simp only [Finset.mem_filter, Finset.mem_range]
      have hlt : n - tri k < k + 1 := by rw [tri_succ] at h2; omega
      refine ⟨hlt, ?_⟩
      rw [seq_eq_of_mem_block h1 h2] at h3
      simpa using h3
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hj1, hj2⟩ := hj
      have h1 : tri k ≤ j + tri k := Nat.le_add_left _ _
      have h2 : j + tri k < tri (k + 1) := by rw [tri_succ]; omega
      simp only [Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨h1, h2⟩, ?_⟩
      rw [seq_eq_of_mem_block h1 h2]
      have hjj : j + tri k - tri k = j := by omega
      rw [hjj]
      simpa using hj2
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      omega
    · intro j _
      omega
  rw [cnt, cnt, hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj, hcard]

