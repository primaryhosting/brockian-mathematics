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

