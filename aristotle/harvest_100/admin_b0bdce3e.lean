/-
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math2

/-- The six dimensions in which framed manifolds of Kervaire invariant one are
known to exist: `2, 6, 14, 30, 62, 126`. -/
def kervaireDims : Finset ℕ := {2, 6, 14, 30, 62, 126}

/-- Arithmetic content of the dimension list: the numbers `2 ^ j - 2` for
`2 ≤ j ≤ 7` are exactly `2, 6, 14, 30, 62, 126`. -/
theorem mem_kervaireDims_iff (n : ℕ) :
    n ∈ kervaireDims ↔ ∃ j : ℕ, 2 ≤ j ∧ j ≤ 7 ∧ n + 2 = 2 ^ j := by
  constructor
  · intro hn
    simp only [kervaireDims, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨4, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨6, by norm_num⟩
    · exact ⟨7, by norm_num⟩
  · rintro ⟨j, hj2, hj7, hn⟩
    simp only [kervaireDims, Finset.mem_insert, Finset.mem_singleton]
    interval_cases j <;> norm_num at hn <;> omega

/--
**The Kervaire invariant problem (statement form).**

Let `KervaireInvariantOne n` be the assertion that there exists an `n`-dimensional
framed manifold of Kervaire invariant one.  Two deep inputs pin down the possible
dimensions:

* **Browder's theorem** (`browder`): such a manifold can only exist when
  `n + 2 = 2 ^ j` for some `j ≥ 2`, i.e. `n = 2 ^ j - 2`;
* **Hill–Hopkins–Ravenel** (`hhr`), together with the resolution of the case
  `j = 7` (dimension 126): there is no such manifold in dimension `2 ^ j - 2`
  once `j ≥ 8`.

Given these two inputs, the Kervaire invariant can be nonzero only in the six
dimensions `2, 6, 14, 30, 62, 126`.  This theorem carries out that deduction; the
two deep geometric/homotopy-theoretic inputs are taken as hypotheses on the
abstract predicate `KervaireInvariantOne`, since neither is available in Mathlib.
-/
theorem kervaire_invariant
    (KervaireInvariantOne : ℕ → Prop)
    (browder : ∀ n : ℕ, KervaireInvariantOne n → ∃ j : ℕ, 2 ≤ j ∧ n + 2 = 2 ^ j)
    (hhr : ∀ j : ℕ, 8 ≤ j → ¬ KervaireInvariantOne (2 ^ j - 2)) :
    ∀ n : ℕ, KervaireInvariantOne n →
      n ∈ ({2, 6, 14, 30, 62, 126} : Finset ℕ) := by
  intro n hn
  obtain ⟨j, hj2, hj⟩ := browder n hn
  rcases le_or_gt j 7 with hle | hgt
  · have : n ∈ kervaireDims := (mem_kervaireDims_iff n).mpr ⟨j, hj2, hle, hj⟩
    simpa [kervaireDims] using this
  · exact absurd (show KervaireInvariantOne (2 ^ j - 2) by
      have h : 2 ^ j - 2 = n := by omega
      rwa [h]) (hhr j hgt)

/-- The hypotheses of `kervaire_invariant` are consistent: the predicate that holds
exactly on `{2, 6, 14, 30, 62, 126}` satisfies both of them.  In particular the
theorem above is not vacuous. -/
theorem kervaire_hypotheses_satisfiable :
    ∃ P : ℕ → Prop,
      (∀ n : ℕ, P n → ∃ j : ℕ, 2 ≤ j ∧ n + 2 = 2 ^ j) ∧
      (∀ j : ℕ, 8 ≤ j → ¬ P (2 ^ j - 2)) ∧ P 2 := by
  refine ⟨fun n => n ∈ kervaireDims, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, hj2, _, hj⟩ := (mem_kervaireDims_iff n).mp hn
    exact ⟨j, hj2, hj⟩
  · intro j hj hmem
    obtain ⟨k, hk2, hk7, hk⟩ := (mem_kervaireDims_iff _).mp hmem
    have h2 : (2 : ℕ) ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    have h3 : (2 : ℕ) ^ k ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) hk7
    have h4 : (2 : ℕ) ≤ 2 ^ j := le_trans (by norm_num) h2
    norm_num at h2 h3
    omega
  · simp [kervaireDims]

end Math2

