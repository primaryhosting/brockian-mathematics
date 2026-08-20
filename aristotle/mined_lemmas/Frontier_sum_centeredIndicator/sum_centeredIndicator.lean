import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

set_option grind.warning false

namespace Frontier

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The "centered indicator" of a finite set `S`: the indicator of `S` minus its mean value.
It is orthogonal to the all-ones vector. -/

lemma sum_centeredIndicator (hV : (Fintype.card V) ≠ 0) (S : Finset V) :
    ∑ i, centeredIndicator S i = 0 := by
  have hn : ((Fintype.card V : ℝ)) ≠ 0 := by exact_mod_cast hV
  simp only [centeredIndicator, Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_univ]
  field_simp
  ring

/-- The squared norm of the centered indicator is `|S| - |S|²/n ≤ |S|`. -/
