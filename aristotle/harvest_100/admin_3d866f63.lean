/-
# Sum Two Squares
Category: Pure Mathematics
Target: Math.sum_two_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

/-- A square is congruent to `0` or `1` modulo `4`. -/
lemma sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rcases Nat.even_or_odd a with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;>
    [left; right] <;> ring_nf <;> omega

/-- **Fermat's two-square theorem.**  A prime `p` is a sum of two squares if and only if
`p = 2` or `p ≡ 1 (mod 4)`. -/
theorem sum_two_squares {p : ℕ} (hp : p.Prime) :
    (∃ a b : ℕ, p = a ^ 2 + b ^ 2) ↔ (p = 2 ∨ p % 4 = 1) := by
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases sq_mod_four a with ha | ha <;> rcases sq_mod_four b with hb | hb
    · exfalso
      have h4 : (4 : ℕ) ∣ a ^ 2 + b ^ 2 := by omega
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp 4 h4) with h | h
      · omega
      · exact absurd (h ▸ hp) (by decide)
    · right; omega
    · right; omega
    · left
      have h2 : (2 : ℕ) ∣ a ^ 2 + b ^ 2 := by omega
      exact ((Nat.Prime.eq_one_or_self_of_dvd hp 2 h2).resolve_left (by omega)).symm
  · rintro (rfl | h)
    · exact ⟨1, 1, by norm_num⟩
    · haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
      exact ⟨a, b, hab.symm⟩

end Math

