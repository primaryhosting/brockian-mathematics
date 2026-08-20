/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A probability distribution on a finite type. -/

lemma convex_domSet (c : A → I → ℝ) : Convex ℝ (domSet c) := by
  rintro y ⟨p, hp, hpy⟩ z ⟨r, hr, hrz⟩ s t hs ht hst
  refine ⟨fun a => s * p a + t * r a,
    ⟨fun a => add_nonneg (mul_nonneg hs (hp.1 a)) (mul_nonneg ht (hr.1 a)), ?_⟩, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hr.2]
    simpa using hst
  · intro i
    have : ∑ a, (s * p a + t * r a) * c a i
        = s * (∑ a, p a * c a i) + t * (∑ a, r a * c a i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this]
    have h1 : s * (∑ a, p a * c a i) ≤ s * y i := mul_le_mul_of_nonneg_left (hpy i) hs
    have h2 : t * (∑ a, r a * c a i) ≤ t * z i := mul_le_mul_of_nonneg_left (hrz i) ht
    simpa [Pi.add_apply, smul_eq_mul] using add_le_add h1 h2

omit [Fintype I] [DecidableEq I] in
