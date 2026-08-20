import Mathlib
/-!
# Legendre sieve: main term with error bound.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve

open ArithmeticFunction Finset

/-- Legendre's identity: the number of `n ∈ [1, x]` coprime to `P` equals
`∑_{d ∣ P} μ(d) ⌊x/d⌋`. -/

lemma term_bound (x d : ℕ) (hd : d ≠ 0) :
    |(moebius d : ℝ) * (((x / d : ℕ) : ℝ) - (x : ℝ) * (d : ℝ)⁻¹)|
      ≤ if Squarefree d then 1 else 0 := by
  by_cases hs : Squarefree d
  · simp only [hs, if_true]
    rw [abs_mul]
    have h1 : |(moebius d : ℝ)| = 1 := by
      have := abs_moebius_eq_one_of_squarefree hs
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    rw [h1, one_mul]
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hle : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) * (d : ℝ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hdR]
      exact_mod_cast Nat.div_mul_le_self x d
    have hgt : (x : ℝ) * (d : ℝ)⁻¹ < ((x / d : ℕ) : ℝ) + 1 := by
      rw [← div_eq_mul_inv, div_lt_iff₀ hdR]
      have hx : x < (x / d + 1) * d := by
        have h1 := Nat.div_add_mod x d
        have h2 := Nat.mod_lt x hdpos
        nlinarith [h1, h2]
      exact_mod_cast hx
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · simp [hs, moebius_eq_zero_of_not_squarefree hs]

/-- The count of integers in `[1, x]` coprime to `P` differs from the heuristic main term
`x · ∏_{p ∣ P} (1 − 1/p)` by at most `2^{ω(P)}` (the number of squarefree divisors of `P`).
(Sanity: `x=10, P=6`: count `=3`, main term `=10·(1/2)(2/3)=10/3`, `|3−10/3|=1/3 ≤ 4 = 2²`.)
Proof idea: count `= ∑_{d ∣ P} μ(d) ⌊x/d⌋` (Legendre); main term `= ∑_{d ∣ P} μ(d) · x/d`; the
difference is `∑_{d ∣ P} μ(d)(⌊x/d⌋ − x/d)` with each term of absolute value `< 1`, and there are
`2^{ω(P)}` nonzero (squarefree-`d`) terms. -/
