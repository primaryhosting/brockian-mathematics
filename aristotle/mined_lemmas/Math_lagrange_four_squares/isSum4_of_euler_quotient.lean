/-
# Lagrange Four Squares
Category: Pure Mathematics
Target: Math.lagrange_four_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` commands to precede any module docstring (`/-! ... -/`),
-- so the header above is written as an ordinary block comment.

import Mathlib

/-!
This file contains a self-contained proof of Lagrange's four-square theorem, following
Lagrange's classical descent argument:

* `Math.euler_identity` : Euler's four-square identity;
* `Math.IsSum4.mul` : the sums of four squares are closed under multiplication;
* `Math.exists_mul_isSum4_of_prime` : some multiple `m * p` with `0 < m < p` of a prime `p`
  is a sum of four squares;
* `Math.isSum4_of_two_mul` and `Math.descent_odd` : the two descent steps;
* `Math.prime_isSum4` : every prime is a sum of four squares;
* `Math.lagrange_four_squares` : every natural number is a sum of four squares.
-/

namespace Math

/-- `IsSum4 n` states that the integer `n` is a sum of four integer squares. -/

private theorem isSum4_of_euler_quotient {m p r A B C D α β γ δ : ℤ} (hm : m ≠ 0)
    (hN : A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2 = m * r)
    (h : (A + m * α) ^ 2 + (B + m * β) ^ 2 + (C + m * γ) ^ 2 + (D + m * δ) ^ 2 = m * p) :
    IsSum4 (r * p) := by
  set a := A + m * α with ha
  set b := B + m * β with hb
  set c := C + m * γ with hc
  set d := D + m * δ with hd
  refine ⟨r + (α * A + β * B + γ * C + δ * D), α * B - β * A + γ * D - δ * C,
    α * C - β * D - γ * A + δ * B, α * D + β * C - γ * B - δ * A, ?_⟩
  refine mul_left_cancel₀ (pow_ne_zero 2 hm) ?_
  have e1 : m * (r + (α * A + β * B + γ * C + δ * D)) = a * A + b * B + c * C + d * D := by
    rw [ha, hb, hc, hd]; linear_combination -hN
  have e2 : m * (α * B - β * A + γ * D - δ * C) = a * B - b * A + c * D - d * C := by
    rw [ha, hb, hc, hd]; ring
  have e3 : m * (α * C - β * D - γ * A + δ * B) = a * C - b * D - c * A + d * B := by
    rw [ha, hb, hc, hd]; ring
  have e4 : m * (α * D + β * C - γ * B - δ * A) = a * D + b * C - c * B - d * A := by
    rw [ha, hb, hc, hd]; ring
  have key : m ^ 2 * ((r + (α * A + β * B + γ * C + δ * D)) ^ 2 +
      (α * B - β * A + γ * D - δ * C) ^ 2 + (α * C - β * D - γ * A + δ * B) ^ 2 +
      (α * D + β * C - γ * B - δ * A) ^ 2)
      = (m * (r + (α * A + β * B + γ * C + δ * D))) ^ 2 + (m * (α * B - β * A + γ * D - δ * C)) ^ 2
        + (m * (α * C - β * D - γ * A + δ * B)) ^ 2
        + (m * (α * D + β * C - γ * B - δ * A)) ^ 2 := by ring
  rw [key, e1, e2, e3, e4, euler_identity, h, hN]
  ring

/-- Descent step for odd `m`. -/
