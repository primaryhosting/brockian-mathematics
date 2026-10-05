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

lemma huangMatrix_flip_self (x : Cube n) (i : Fin n) :
    huangMatrix n (flipAt x i) x = hsign x i := by
  rw [huangMatrix_apply_flip]
  rw [Finset.sum_eq_single i]
  · rw [if_pos (flipAt_flipAt x i), hsign_flipAt_self]
  · intro k _ hk
    rw [if_neg (flipAt_flipAt_ne x hk)]
  · intro h
    exact absurd (Finset.mem_univ i) h

