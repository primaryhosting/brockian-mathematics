import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


lemma hadamard_simonState_eq_zero {n : ℕ} (s x0 y : V n) (h : dotp s y = 1) :
    hadamard (simonState s x0) y = 0 := by
  have hs : s ≠ 0 := by
    intro h0
    rw [h0, dotp_zero_left] at h
    exact absurd h (by decide)
  rw [hadamard_simonState s x0 y hs, dotp_add_left, h, sgn_add]
  have : sgn 1 = -1 := by norm_num [sgn]
  rw [this]
  ring

/-- **Uniformity on `s^⊥`.** Every outcome `y` orthogonal to `s` is observed with
probability `2 / 2ⁿ`. -/
