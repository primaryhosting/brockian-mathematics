import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

lemma odd_iff_cast_zmod_two (m : ℕ) : Odd m ↔ (m : ZMod 2) = 1 := by
  rw [Nat.odd_iff, ← ZMod.natCast_mod m 2]
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
    rcases h2 with h0 | h1
    · rw [h0] at h; simp at h
    · exact h1

/-- If `f` maps a finset `σ` onto `J` and `σ` has exactly one element more than `J`, then
exactly one fibre of `f` over `J` has two elements and all the others are singletons. -/
