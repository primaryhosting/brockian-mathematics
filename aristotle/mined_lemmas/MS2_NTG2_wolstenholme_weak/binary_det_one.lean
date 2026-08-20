import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem binary_det_one {A B C : ℤ} (hA : 0 < A) (hD : 4 * A * C - B ^ 2 = 4) :
    ∃ p q r s : ℤ, ∀ x y : ℤ, qb A B C x y = (p * x + q * y) ^ 2 + (r * x + s * y) ^ 2 := by
  have hD' : 0 < 4 * A * C - B ^ 2 := by omega
  obtain ⟨x₀, y₀, hne0, hle⟩ := lagrange hA hD'
  have hpos : 0 < qb A B C x₀ y₀ := qb_pos hA hD' hne0
  have hone : qb A B C x₀ y₀ = 1 := by nlinarith [hle, hpos]
  have hmin : ∀ x y : ℤ, ¬(x = 0 ∧ y = 0) → qb A B C x₀ y₀ ≤ qb A B C x y := by
    intro x y hxy
    have := qb_pos hA hD' hxy
    omega
  obtain ⟨x₁, y₁, hdet, hB, hC⟩ := reduction hA hD' hne0 hmin
  have key := disc_subst A B C x₀ y₀ x₁ y₁
  rw [hdet, hone, hD] at key
  rw [hone] at hB hC
  set B' : ℤ := 2 * A * x₀ * x₁ + B * (x₀ * y₁ + x₁ * y₀) + 2 * C * y₀ * y₁ with hB'
  -- `4 * qb A B C x₁ y₁ - B'^2 = 4` with `B'^2 ≤ 1`
  have hB2 : B' ^ 2 ≤ 1 := by simpa only [one_pow] using hB
  have hsq : B' ^ 2 = 4 * (qb A B C x₁ y₁ - 1) := by linarith [key]
  have hC1 : qb A B C x₁ y₁ = 1 := le_antisymm (by nlinarith [hsq, hB2, sq_nonneg B']) hC
  have hB0 : B' = 0 := by
    have h0 : B' ^ 2 = 0 := by rw [hsq, hC1]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h0
  refine ⟨y₁, -x₁, -y₀, x₀, ?_⟩
  intro x y
  have hs := qb_subst A B C x₀ y₀ x₁ y₁ (y₁ * x + (-x₁) * y) ((-y₀) * x + x₀ * y)
  rw [hone, ← hB', hB0, hC1] at hs
  have e1 : x₀ * (y₁ * x + -x₁ * y) + x₁ * (-y₀ * x + x₀ * y) = x := by
    have : (x₀ * y₁ - x₁ * y₀) * x = x := by rw [hdet]; ring
    linarith [this]
  have e2 : y₀ * (y₁ * x + -x₁ * y) + y₁ * (-y₀ * x + x₀ * y) = y := by
    have : (x₀ * y₁ - x₁ * y₀) * y = y := by rw [hdet]; ring
    linarith [this]
  rw [e1, e2] at hs
  rw [hs]
  unfold qb
  ring

end ThreeSquares

import Mathlib

/-!
# Construction of a unimodular ternary form representing `n`

For `n` not divisible by `4` and not congruent to `7` mod `8`, we construct integers
`u, M, s` with `M > 0` and

`n * (u * M - s²) - M = 1`,

which is precisely the statement that the symmetric matrix

`!![n, 1, 0; 1, u, -s; 0, -s, M]`

has determinant `1`.  (It is automatically positive definite, see `NTGaps2/ThreeSquares.lean`.)

The construction is the classical one.  Using Dirichlet's theorem on primes in arithmetic
progressions we pick a prime `p` in a suitable residue class, put `M = p` (or `M = 2p` when
`n ≡ 3 mod 8`), `D = (M+1)/n`, and use quadratic reciprocity for the Jacobi symbol to check that
`-D` is a square modulo `M`; writing `s² + D = u M` then gives the required identity.
-/

namespace ThreeSquares

open NumberTheorySymbols

/-! ### Assembling the data -/

/-- If `n * D = M + 1` and `M ∣ s² + D`, we obtain the required data. -/
