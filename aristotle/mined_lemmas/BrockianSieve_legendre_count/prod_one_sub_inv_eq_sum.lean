import Mathlib
/-!
# Legendre sieve: main term with error bound.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib` only.
-/
namespace BrockianSieve

open ArithmeticFunction Finset

/-- Legendre's identity: the number of `n ∈ [1, x]` coprime to `P` equals
`∑_{d ∣ P} μ(d) ⌊x/d⌋`. -/

lemma prod_one_sub_inv_eq_sum (P : ℕ) (hP : P ≠ 0) :
    ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹) = ∑ d ∈ P.divisors, (moebius d : ℝ) * (d : ℝ)⁻¹ := by
  have hL : ∏ p ∈ P.primeFactors, (1 - (p : ℝ)⁻¹)
      = ∑ t ∈ P.primeFactors.powerset, ∏ p ∈ t, (-(p : ℝ)⁻¹) := by
    have := Finset.prod_add (fun p : ℕ => (-(p : ℝ)⁻¹)) (fun _ => (1 : ℝ)) P.primeFactors
    simpa [sub_eq_neg_add] using this
  have hfil : ∑ d ∈ P.divisors, (moebius d : ℝ) * (d : ℝ)⁻¹
      = ∑ d ∈ P.divisors.filter Squarefree, (moebius d : ℝ) * (d : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hs : Squarefree d
    · simp [hs]
    · simp [hs, moebius_eq_zero_of_not_squarefree hs]
  have h2 : (UniqueFactorizationMonoid.normalizedFactors P).toFinset = P.primeFactors := by
    rw [Nat.factors_eq]; rfl
  have hR := Nat.sum_divisors_filter_squarefree (n := P) hP
    (f := fun d => (moebius d : ℝ) * (d : ℝ)⁻¹)
  rw [h2] at hR
  rw [hL, hfil, hR]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Finset.mem_powerset] at ht
  have hprod : t.val.prod = ∏ p ∈ t, p := by rw [Finset.prod_eq_multiset_prod]; simp
  simp only [hprod]
  have hcop : (↑t : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
    intro a ha b hb hab
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (ht ha))
      (Nat.prime_of_mem_primeFactors (ht hb))).2 hab
  have hmu : (moebius (∏ p ∈ t, p) : ℤ) = ∏ p ∈ t, (moebius p) :=
    isMultiplicative_moebius.map_prod (fun p : ℕ => p) t hcop
  have hmu' : ((moebius (∏ p ∈ t, p) : ℤ) : ℝ) = ∏ p ∈ t, (-1 : ℝ) := by
    rw [hmu]
    push_cast
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [moebius_apply_prime (Nat.prime_of_mem_primeFactors (ht hp))]
    norm_num
  rw [hmu', Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by ring

/-- The number of squarefree divisors of `P` is `2 ^ ω(P)`. -/
