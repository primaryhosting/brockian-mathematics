import Mathlib

/-!
# Hückel π-energies of the cycle graph `C n`

The adjacency (Hückel) matrix of the cycle graph `C n` (`n ≥ 3`) has spectrum
`{2 cos (2 π k / n) : k = 0, …, n-1}`, and its characteristic polynomial is
`∏ k, (X - 2 cos (2 π k / n))`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

lemma cycleRoot_pow_congr {n a b : ℕ} (hn : n ≠ 0) (h : a % n = b % n) :
    cycleRoot n ^ a = cycleRoot n ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  conv_rhs => rw [← Nat.div_add_mod b n]
  rw [pow_add, pow_add, pow_mul, pow_mul, cycleRoot_pow_card hn, one_pow, one_pow, h]

/-- Stepping one vertex along the cycle multiplies the `k`-th eigenvector entry by `ω ^ k`. -/
