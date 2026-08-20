import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

theorem isUpperMoebius_muPlus {k : ℕ} (hk : Even k) :
    BoundingSieve.IsUpperMoebius (muPlus k) := by
  intro n
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [muPlus]
  rw [if_neg hn1]
  -- restrict to squarefree divisors
  have h1 : ∑ d ∈ n.divisors, muPlus k d = ∑ d ∈ n.divisors with Squarefree d, muPlus k d := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hsq : Squarefree d
    · simp [hsq]
    · simp [hsq, muPlus, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  have hfac : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    rw [Nat.factors_eq, ← Nat.toFinset_factors n]
    rfl
  rw [h1, Nat.sum_divisors_filter_squarefree hn0, hfac]
  let F := n.primeFactors
  have hm : F.card = n.primeFactors.card := rfl
  -- evaluate the weights on products of subsets of the prime factors
  have hval : ∀ S ∈ F.powerset, muPlus k (S.val.prod) =
      if S.card ≤ k then (-1 : ℝ) ^ S.card else 0 := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
    have hprod : S.val.prod = ∏ p ∈ S, p := by
      rw [← Finset.prod_map_val S (fun p => p), Multiset.map_id']
    have hpf : (∏ p ∈ S, p).primeFactors = S := Nat.primeFactors_prod hprime
    have hcop : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
      intro a ha b hb hab
      exact (Nat.coprime_primes (hprime a ha) (hprime b hb)).mpr hab
    have hmu : ArithmeticFunction.moebius (∏ p ∈ S, p) = (-1 : ℤ) ^ S.card := by
      rw [show (∏ p ∈ S, p) = ∏ p ∈ S, id p from rfl,
        ArithmeticFunction.isMultiplicative_moebius.map_prod id S hcop]
      simp only [id_eq]
      rw [Finset.prod_congr rfl (fun p hp => ArithmeticFunction.moebius_apply_prime (hprime p hp))]
      simp
    rw [hprod, muPlus, hpf, hmu]
    split <;> simp
  rw [Finset.sum_congr rfl hval, Finset.sum_powerset]
  -- group by cardinality
  have hgroup : ∀ j ∈ range (F.card + 1),
      (∑ S ∈ Finset.powersetCard j F, if S.card ≤ k then (-1 : ℝ) ^ S.card else 0)
        = (if j ≤ k then (-1 : ℝ) ^ j * (F.card.choose j) else 0) := by
    intro j _
    rw [Finset.sum_congr rfl (fun S hS => by
      rw [(Finset.mem_powersetCard.mp hS).2])]
    rw [Finset.sum_const, Finset.card_powersetCard]
    split <;> simp [mul_comm]
  rw [Finset.sum_congr rfl hgroup]
  -- compare with the truncated alternating sum
  have hmpos : 1 ≤ F.card := by
    have : F.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
    exact Finset.card_pos.mpr this
  obtain ⟨m', hm'⟩ : ∃ m', F.card = m' + 1 := ⟨F.card - 1, by omega⟩
  rw [hm']
  have key : ∑ j ∈ range (m' + 1 + 1), (if j ≤ k then (-1 : ℝ) ^ j * ((m' + 1).choose j) else 0)
      = ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ((m' + 1).choose j) := by
    rcases le_or_gt (m' + 1) k with hcase | hcase
    · -- the truncation is vacuous
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [if_pos (by simp only [Finset.mem_range] at hj; omega)])]
      refine Finset.sum_subset (by
        intro j hj
        simp only [Finset.mem_range] at hj ⊢
        omega) ?_
      intro j hj hj'
      simp only [Finset.mem_range, not_lt] at hj hj'
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · -- the truncation cuts the sum at `k < m' + 1`
      have h2 : ∑ j ∈ range (m' + 1 + 1), (if j ≤ k then (-1 : ℝ) ^ j * ((m' + 1).choose j) else 0)
          = ∑ j ∈ range (k + 1), (if j ≤ k then (-1 : ℝ) ^ j * ((m' + 1).choose j) else 0) := by
        refine (Finset.sum_subset (by
          intro j hj
          simp only [Finset.mem_range] at hj ⊢
          omega) ?_).symm
        intro j hj hj'
        simp only [Finset.mem_range, not_lt] at hj hj'
        rw [if_neg (by omega)]
      rw [h2]
      exact Finset.sum_congr rfl fun j hj => by
        rw [if_pos (by simp only [Finset.mem_range] at hj; omega)]
  rw [key]
  have hint : ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ((m' + 1).choose j)
      = ((∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * ((m' + 1).choose j) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hint, alternating_sum_choose m' k]
  have : (0:ℤ) ≤ (-1) ^ k * (m'.choose k) := by
    rw [hk.neg_one_pow]
    positivity
  exact_mod_cast this

end Brun

import Mathlib

/-!
# Counting solutions of `d ∣ n(n+2)` in an interval

For odd squarefree `d`, the congruence `n(n+2) ≡ 0 (mod d)` has exactly `2 ^ ω(d)` solutions
modulo `d` (`Brun.card_sols`), hence the number of `n ∈ [1, x]` with `d ∣ n(n+2)` is
`x · 2^ω(d)/d` up to an error of at most `2 · 2^ω(d)` (`Brun.abs_count_sub_le`).
-/

open Finset

namespace Brun

/-- The set of residues `r < d` with `d ∣ r (r + 2)`. -/
