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
theorem sum_two_squares {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, p = a ^ 2 + b ^ 2) ↔ (p = 2 ∨ p % 4 = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨a, b, rfl⟩
    have h4 : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
      have := sq_mod_four a
      have := sq_mod_four b
      omega
    have := hp.eq_two_or_odd
    omega
  · intro h
    have h4 : p % 4 ≠ 3 := by omega
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq h4
    exact ⟨a, b, hab.symm⟩

end Math

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

