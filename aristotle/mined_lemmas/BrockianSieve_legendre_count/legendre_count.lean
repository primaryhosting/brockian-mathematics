import Mathlib
/-!
# Legendre sieve: main term with error bound.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve

open ArithmeticFunction Finset

/-- Legendre's identity: the number of `n ∈ [1, x]` coprime to `P` equals
`∑_{d ∣ P} μ(d) ⌊x/d⌋`. -/

lemma legendre_count (x P : ℕ) (hP : P ≠ 0) :
    ((((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℤ))
      = ∑ d ∈ P.divisors, (moebius d : ℤ) * ((x / d : ℕ) : ℤ) := by
  have hdelta : ∀ n : ℕ, ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
    intro n
    rw [← ArithmeticFunction.coe_mul_zeta_apply (f := (moebius : ArithmeticFunction ℤ)) (x := n),
      moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := by
    ext n; simp [Nat.lt_iff_add_one_le]
  have step1 : ((((Finset.Icc 1 x).filter (fun n => Nat.Coprime n P)).card : ℤ))
      = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ P.divisors, (if d ∣ n then (moebius d : ℤ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hgcd : (Nat.gcd n P).divisors = P.divisors.filter (· ∣ n) := by
      ext d
      simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hP, Nat.gcd_eq_zero_iff, hn0]
      tauto
    have h := hdelta (Nat.gcd n P)
    rw [hgcd, Finset.sum_filter] at h
    rw [← h]
  rw [step1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  rw [hIcc]
  exact_mod_cast congrArg (fun m : ℕ => (m : ℤ)) (Nat.Ioc_filter_dvd_card_eq_div x d)

/-- Expanding the product over the prime factors of `P`:
`∏_{p ∣ P} (1 - 1/p) = ∑_{d ∣ P} μ(d)/d`. -/
