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


lemma adversaryOracle_shift {n : ℕ} (Q : Finset (V n)) (s : V n) (i0 : Fin n)
    (hi0 : s i0 = 1) (hQ : ∀ a ∈ Q, a + s ∉ Q) (x : V n) :
    adversaryOracle Q s i0 (x + s) = adversaryOracle Q s i0 x := by
  have hcancel : x + s + s = x := add_add_cancel_cube x s
  have hcoord : (x + s) i0 = x i0 + 1 := by simp [hi0]
  unfold adversaryOracle
  by_cases h1 : x ∈ Q
  · have h2 : x + s ∉ Q := hQ x h1
    simp [h1, h2, hcancel]
  · by_cases h2 : x + s ∈ Q
    · simp [h1, h2]
    · have h3 : x + s + s ∉ Q := by rwa [hcancel]
      rcases zmod2_cases (x i0) with h4 | h4
      · have h5 : (x + s) i0 ≠ 0 := by rw [hcoord, h4]; decide
        rw [if_neg h2, if_neg h3, if_neg h5, if_neg h1, if_neg h2, if_pos h4, hcancel]
      · have h5 : (x + s) i0 = 0 := by rw [hcoord, h4]; decide
        have h6 : x i0 ≠ 0 := by rw [h4]; decide
        rw [if_neg h2, if_neg h3, if_pos h5, if_neg h1, if_neg h2, if_neg h6]

