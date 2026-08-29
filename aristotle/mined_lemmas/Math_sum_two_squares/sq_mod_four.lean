/-
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Math

/-- Squares are `0` or `1` mod `4`. -/

theorem sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  obtain ⟨k, hk | hk⟩ : ∃ k, a = 2 * k ∨ a = 2 * k + 1 := ⟨a / 2, by omega⟩
  · left
    have : a ^ 2 = 4 * k ^ 2 := by subst hk; ring
    omega
  · right
    have : a ^ 2 = 4 * (k ^ 2 + k) + 1 := by subst hk; ring
    omega

/-- **Fermat's two-squares theorem.** A prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 (mod 4)`.

The hard direction uses Mathlib's `Nat.Prime.sq_add_sq` (Fermat's Christmas theorem: every
prime `p` with `p % 4 ≠ 3` is a sum of two squares). The easy direction follows from the fact
that squares are `0` or `1` mod `4`, together with `Nat.Prime.eq_two_or_odd`. -/
