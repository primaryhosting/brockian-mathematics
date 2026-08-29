import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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

/-- `A` contains an arithmetic progression of length `k`, i.e. there are `a` and a positive
common difference `d` with `a, a + d, …, a + (k-1) * d` all in `A`. -/

lemma hasAPOfLength_of_le {A : Set ℕ} {k l : ℕ} (hkl : k ≤ l) (h : HasAPOfLength A l) :
    HasAPOfLength A k := by
  obtain ⟨a, d, hd, h⟩ := h
  exact ⟨a, d, hd, fun i hi => h i (lt_of_lt_of_le hi hkl)⟩

/-- A nontrivial solution of `x + z = y + y` inside `A` yields a `3`-term progression in `A`. -/
