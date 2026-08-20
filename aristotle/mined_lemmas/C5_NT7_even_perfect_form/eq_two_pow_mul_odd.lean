import Mathlib
namespace C5.NT7

open ArithmeticFunction Finset

open scoped sigma

/-- `σ 1 (2 ^ k) = 2 ^ (k + 1) - 1`, i.e. the sum of divisors of a power of two is the
corresponding Mersenne number. -/

private theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) :
    ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  refine ⟨multiplicity 2 n, m, hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Euler's theorem** (the hard direction of the Euclid–Euler theorem): an even perfect
number is of the form `2 ^ k * (2 ^ (k + 1) - 1)` with `2 ^ (k + 1) - 1` prime.

This is the argument of Theorem 70 of the *100 theorems* list, reproduced here since the
Mathlib archive is not available through a bare `import Mathlib`. -/
