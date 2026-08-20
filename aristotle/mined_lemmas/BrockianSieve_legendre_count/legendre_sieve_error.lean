import Mathlib
/-!
# Legendre sieve: main term with error bound.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve

open ArithmeticFunction Finset

/-- Legendre's identity: the number of `n ∈ [1, x]` coprime to `P` equals
`∑_{d ∣ P} μ(d) ⌊x/d⌋`. -/

theorem legendre_sieve_error (x P : ℕ) (hP : P ≠ 0) :
    |(((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℝ)
        - (x : ℝ) * ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)|
      ≤ (2 : ℝ) ^ P.primeFactors.card := by
  have hcount : (((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℝ)
      = ∑ d ∈ P.divisors, (moebius d : ℝ) * ((x / d : ℕ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) (legendre_count x P hP)
    push_cast at this
    exact this
  have hmain : (x : ℝ) * ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)
      = ∑ d ∈ P.divisors, (moebius d : ℝ) * ((x : ℝ) * (d : ℝ)⁻¹) := by
    rw [prod_one_sub_inv_eq_sum P hP, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => by ring
  rw [hcount, hmain, ← Finset.sum_sub_distrib]
  have hle : |∑ d ∈ P.divisors, ((moebius d : ℝ) * ((x / d : ℕ) : ℝ)
        - (moebius d : ℝ) * ((x : ℝ) * (d : ℝ)⁻¹))|
      ≤ ∑ d ∈ P.divisors, (if Squarefree d then (1 : ℝ) else 0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
    have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_mem_divisors hd)
    calc |(moebius d : ℝ) * ((x / d : ℕ) : ℝ) - (moebius d : ℝ) * ((x : ℝ) * (d : ℝ)⁻¹)|
        = |(moebius d : ℝ) * (((x / d : ℕ) : ℝ) - (x : ℝ) * (d : ℝ)⁻¹)| := by ring_nf
      _ ≤ _ := term_bound x d hd0
  refine hle.trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one, mul_zero, add_zero]
  rw [card_squarefree_divisors P hP]
  push_cast
  ring_nf
  rfl

end BrockianSieve

