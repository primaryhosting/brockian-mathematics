/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
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

open Finset

/-- `A` has positive upper density: there is `δ > 0` such that infinitely many initial
segments `{0, …, n-1}` meet `A` in at least `δ * n` elements. -/

def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    δ * n ≤ #((Finset.range n).filter (fun x => x ∈ A))

/-- `A` contains an arithmetic progression of length `k` with positive common difference. -/
