/-
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Smirnov Percolation
Category: Frontier — Fields Medal Work
Target: Frontier.smirnov_percolation
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

/-- A real Möbius transformation `x ↦ (a x + b) / (c x + d)`.  These are exactly the
boundary values on `ℝ = ∂ℍ` of the conformal automorphisms of the upper half-plane. -/

lemma mobius_injective {a b c d x y : ℝ} (hdet : a * d - b * c ≠ 0)
    (hx : c * x + d ≠ 0) (hy : c * y + d ≠ 0)
    (h : mobius a b c d x = mobius a b c d y) : x = y := by
  have h0 : mobius a b c d x - mobius a b c d y = 0 := by rw [h]; ring
  rw [mobius_sub hx hy, div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · rcases mul_eq_zero.1 h0 with h1 | h1
    · exact absurd h1 hdet
    · linarith [sub_eq_zero.1 h1]
  · exact absurd h0 (mul_ne_zero hx hy)

