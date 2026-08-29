import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

variable {Ω : Type*} [DecidableEq Ω]

/-- The probability of the (finite) event `S` under the weight function `p`. -/

private lemma unif_post (S T : Finset (Fin 4)) (hT : 0 < T.card) :
    prob unif S / prob unif T = (S.card : ℝ) / (T.card : ℝ) := by
  have hne : (T.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  rw [prob_unif, prob_unif]
  field_simp

/-- All hypotheses of `Frontier.aumann_agreement` hold simultaneously in a non-degenerate
example with two distinct information partitions, so the theorem is not vacuous. -/
