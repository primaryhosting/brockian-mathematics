/-
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gale Stewart Open
Category: Frontier — Set Theory
Target: Frontier.Gale_Stewart_open
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

variable {A : Type*}

/-- The finite position consisting of the first `n` moves of the play `x`. -/

lemma playOf_eq (n : ℕ) :
    playOf σ τ n = if Even n then σ (runPos σ τ n) else τ (runPos σ τ n) := by
  have h : (runPos σ τ (n + 1))[n]'(by simp) =
      (runPos σ τ n ++ [if Even n then σ (runPos σ τ n) else τ (runPos σ τ n)])[n]'(by simp) := by
    congr 1
  rw [playOf, h]
  simp

