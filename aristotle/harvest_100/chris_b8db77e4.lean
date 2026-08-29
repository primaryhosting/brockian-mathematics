/-
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
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

namespace Math

/-- **Fermat's two-square theorem.** A prime `p` is a sum of two squares of natural
numbers if and only if `p = 2` or `p ≡ 1 (mod 4)`. -/
theorem sum_two_squares (p : ℕ) (hp : Nat.Prime p) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = p) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, hab⟩
    -- Squares are `0` or `1` mod `4`, so a sum of two squares is never `3` mod `4`.
    have h4 : p % 4 ≠ 3 := by
      intro h3
      have key : ((a : ZMod 4) ^ 2 + (b : ZMod 4) ^ 2) = ((p : ℕ) : ZMod 4) := by
        push_cast [← hab]; ring
      have hp4 : ((p : ℕ) : ZMod 4) = 3 := by
        rw [← ZMod.natCast_mod, h3]; rfl
      rw [hp4] at key
      revert key
      generalize (a : ZMod 4) = x
      generalize (b : ZMod 4) = y
      revert x y
      decide
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact Or.inl h2
    · right; omega
  · intro h
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    exact Nat.Prime.sq_add_sq (by omega)

end Math

