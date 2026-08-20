import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem gauss_eureka (n : ℕ) : ∃ a b c : ℕ, n = a*(a+1)/2 + b*(b+1)/2 + c*(c+1)/2 := by
  obtain ⟨x, y, z, hxyz⟩ := legendre_three_square (8*n+3) (by
    rintro ⟨a, b, hab⟩
    rcases a with _ | a
    · simp at hab; omega
    · have h4 : (4:ℕ) ∣ 8*n+3 := ⟨4^a*(8*b+7), by rw [hab]; ring⟩
      omega)
  -- a sum of three squares which is `3` mod `4` must have all three summands odd
  have hx := sq_mod4 x
  have hy := sq_mod4 y
  have hz := sq_mod4 z
  have hxo : x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1 := by omega
  obtain ⟨a, ha⟩ : ∃ a, x = 2*a+1 := ⟨x/2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, y = 2*b+1 := ⟨y/2, by omega⟩
  obtain ⟨c, hc⟩ : ∃ c, z = 2*c+1 := ⟨z/2, by omega⟩
  refine ⟨a, b, c, ?_⟩
  subst ha hb hc
  have e : (2*a+1)^2+(2*b+1)^2+(2*c+1)^2 = 4*(a*(a+1) + b*(b+1) + c*(c+1)) + 3 := by ring
  have da : 2 * (a*(a+1)/2) = a*(a+1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self a)
  have db : 2 * (b*(b+1)/2) = b*(b+1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self b)
  have dc : 2 * (c*(c+1)/2) = c*(c+1) := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self c)
  omega

end MS2.NTG2

import Mathlib

/-!
# Positive definite integral binary quadratic forms

We develop just enough of the classical reduction theory of binary quadratic forms
`A x² + B x y + C y²` to obtain Lagrange's bound `3 m² ≤ 4AC - B²` for some nonzero value `m`,
and the fact that a positive definite form with `4AC - B² = 4` is a sum of two squares
of integral linear forms.
-/

namespace ThreeSquares

/-- The binary quadratic form `A x² + B x y + C y²`. -/
