import Mathlib

/-!
# Superperfect numbers (Brockian corpus)

A natural number `n` is **superperfect** when `σ(σ(n)) = 2n`, where `σ` is the
sum-of-divisors function.  We spell `σ` directly as `sig n = ∑ d ∈ n.divisors, d`
(the `Nat.sigma` name is not available in this Mathlib environment; this Finset-sum
definition is the standard σ₁).

The even superperfect numbers are exactly `2^(p-1)` where `2^p − 1` is a Mersenne prime
(Suryanarayana / Kanold). Here we verify the first few instances concretely, and record
one honest non-example (`8` is a power of two but NOT superperfect: `2^4 − 1 = 15` is not
prime, so `σ(σ(8)) = σ(15) = 24 ≠ 16`).
-/

namespace Brockian.Superperfect

/-- Sum-of-divisors function `σ₁`. -/
def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

-- σ(2)  = 3,  σ(3)   = 4   = 2·2   (Mersenne prime 2^2−1 = 3)
theorem superperfect_2  : sig (sig 2)  = 2 * 2  := by decide

-- σ(4)  = 7,  σ(7)   = 8   = 2·4   (Mersenne prime 2^3−1 = 7)
theorem superperfect_4  : sig (sig 4)  = 2 * 4  := by decide

-- σ(16) = 31, σ(31)  = 32  = 2·16  (Mersenne prime 2^5−1 = 31)
theorem superperfect_16 : sig (sig 16) = 2 * 16 := by decide

-- σ(64) = 127, σ(127) = 128 = 2·64  (Mersenne prime 2^7−1 = 127)
theorem superperfect_64 : sig (sig 64) = 2 * 64 := by decide

-- Honesty: not every power of two is superperfect.
-- σ(8) = 15, σ(15) = 24 ≠ 16  (2^4−1 = 15 = 3·5 is composite)
theorem not_superperfect_8 : sig (sig 8) ≠ 2 * 8 := by decide

/-- The four superperfect witnesses `2, 4, 16, 64`, bundled. -/
theorem superperfect_examples :
    sig (sig 2)  = 2 * 2  ∧ sig (sig 4)  = 2 * 4  ∧
    sig (sig 16) = 2 * 16 ∧ sig (sig 64) = 2 * 64 :=
  ⟨superperfect_2, superperfect_4, superperfect_16, superperfect_64⟩

end Brockian.Superperfect
