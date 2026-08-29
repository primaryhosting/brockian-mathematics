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
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

open Finset

/-- The trace of a set `A ⊆ ℕ` on the initial segment `{0, 1, ..., N - 1}`. -/

lemma mem_of_mem_trace {A : Set ℕ} {N x : ℕ} (hx : x ∈ trace A N) : x ∈ A := by
  simp only [trace, Finset.mem_filter] at hx
  exact hx.2

/-- `A ⊆ ℕ` has positive upper density: there is `δ > 0` such that the density of `A` in
`{0, ..., N-1}` is at least `δ` for infinitely many `N`.  This is exactly the statement that the
upper density `limsup_N |A ∩ [0,N)| / N` is positive. -/
