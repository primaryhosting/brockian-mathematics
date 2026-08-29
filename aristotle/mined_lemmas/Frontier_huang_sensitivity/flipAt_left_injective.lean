import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

open Finset
open scoped Matrix

/-! ## The Boolean hypercube -/

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a hypercube vertex. -/

lemma flipAt_left_injective (x : Cube n) {i k : Fin n} (h : flipAt x i = flipAt x k) : i = k := by
  by_contra hik
  have h1 : flipAt x i i = flipAt x k i := congrArg (fun z => z i) h
  rw [flipAt_self, flipAt_of_ne _ hik] at h1
  simp at h1

/-! ## Huang's signed adjacency matrix -/

/-- The number of coordinates above `i` at which `x` is `true`. -/
