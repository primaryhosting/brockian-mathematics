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

lemma hsign_flipAt_lt (x : Cube n) {i k : Fin n} (h : i < k) :
    hsign (flipAt x k) i = - hsign x i := by
  by_cases hk : x k = true
  · have hc := hcount_flipAt_lt_of_true x h hk
    simp only [hsign, hc, pow_succ]
    ring
  · have hk' : (flipAt x k) k = true := by
      simp only [Bool.not_eq_true] at hk
      simp [hk]
    have hc := hcount_flipAt_lt_of_true (flipAt x k) h hk'
    rw [flipAt_flipAt] at hc
    simp only [hsign, hc, pow_succ]
    ring

