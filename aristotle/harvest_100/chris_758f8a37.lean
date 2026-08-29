/-
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Math

/-- **Fermat's two-squares theorem.** A prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 (mod 4)`.

The hard direction (every prime `p` with `p % 4 ≠ 3` is a sum of two squares) is Mathlib's
`Nat.Prime.sq_add_sq`; the easy direction uses that squares are `0` or `1` mod `4`. -/
theorem sum_two_squares {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, p = a ^ 2 + b ^ 2) ↔ p = 2 ∨ p % 4 = 1 := by
  have key : ∀ n : ℕ, n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
    intro n
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · left
      have h : n ^ 2 = 4 * k ^ 2 := by subst hk; ring
      simp [h, Nat.mul_mod_right]
    · right
      have h : n ^ 2 = 4 * (k ^ 2 + k) + 1 := by subst hk; ring
      simp [h]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact Or.inl h2
    · right
      rcases key a with ha | ha <;> rcases key b with hb | hb <;> omega
  · rintro (rfl | h)
    · exact ⟨1, 1, by norm_num⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
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

