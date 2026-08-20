/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

namespace Frontier

variable {n : ℕ}

/-- The *centered indicator* of a vertex set `S` inside a vertex set of size `n`:
the indicator function of `S` minus its mean value `|S|/n`.  It is orthogonal to
the all-ones vector. -/

lemma sum_sq_centeredIndicator (hn : 0 < n) (S : Finset (Fin n)) :
    ∑ i, centeredIndicator S i ^ 2 = (S.card : ℝ) - (S.card : ℝ) ^ 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsq : ∀ i : Fin n, centeredIndicator S i ^ 2
      = (if i ∈ S then (1 : ℝ) else 0)
        - 2 * (S.card : ℝ) / (n : ℝ) * (if i ∈ S then (1 : ℝ) else 0)
        + (S.card : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
    intro i
    by_cases h : i ∈ S <;> simp [centeredIndicator, h] <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hsq i)]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.card_univ]
  field_simp
  ring

/-- The squared euclidean norm of the centered indicator is at most `|S|`. -/
