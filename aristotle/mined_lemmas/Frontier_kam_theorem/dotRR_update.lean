import Mathlib
/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

namespace Frontier

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/

lemma dotRR_update (c x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    dotRR c (Function.update x j t) = dotRR c x + c j * (t - x j) := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      c i * Function.update x j t i = c i * x i + (if i = j then c j * (t - x j) else 0) := by
    intro i _
    by_cases h : i = j
    · subst h; simp [Function.update_self]; ring
    · simp [h]
  rw [dotRR, dotRR, Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

