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

lemma sum_centeredIndicator (hn : 0 < n) (S : Finset (Fin n)) :
    ∑ i, centeredIndicator S i = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp [centeredIndicator, Finset.sum_sub_distrib, Finset.card_univ]
  field_simp
  ring

/-- The squared euclidean norm of the centered indicator of `S` is `|S| - |S|²/n`. -/
