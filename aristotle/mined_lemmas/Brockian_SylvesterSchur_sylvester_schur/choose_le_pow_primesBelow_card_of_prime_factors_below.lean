import Mathlib
import SylvesterSchurCore
namespace Brockian.SylvesterSchur
/-- Sylvester–Schur: for n > k ≥ 1, some element of {n+1,…,n+k} has a prime factor > k. -/

lemma choose_le_pow_primesBelow_card_of_prime_factors_below
    {N k : ℕ} (hkn : k ≤ N) (hN : 0 < N)
    (hsmall : ∀ p : ℕ, p.Prime → p ∣ Nat.choose N k → p < k + 1) :
    Nat.choose N k ≤ N ^ (k + 1).primesBelow.card := by
  classical
  let s := (Finset.range (N + 1)).filter (fun p => p ∈ (k + 1).primesBelow)
  let f := fun p => p ^ (Nat.choose N k).factorization p
  have hs_subset : s ⊆ Finset.range (N + 1) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hprod_eq : (∏ p ∈ Finset.range (N + 1), f p) = ∏ p ∈ s, f p := by
    symm
    refine Finset.prod_subset hs_subset ?_
    intro p hp_range hp_not_s
    have hp_not_primesBelow : p ∉ (k + 1).primesBelow := by
      intro hp_mem
      exact hp_not_s (by simp [s, hp_range, hp_mem])
    by_cases hfac : (Nat.choose N k).factorization p = 0
    · simp [f, hfac]
    · have hp_prime : p.Prime := by
        by_contra hp_not_prime
        exact hfac (Nat.factorization_eq_zero_of_not_prime (Nat.choose N k) hp_not_prime)
      have hp_dvd : p ∣ Nat.choose N k := Nat.dvd_of_factorization_pos hfac
      exact (hp_not_primesBelow (Nat.mem_primesBelow.mpr ⟨hsmall p hp_prime hp_dvd, hp_prime⟩)).elim
  have hs_card : s.card ≤ (k + 1).primesBelow.card := by
    refine Finset.card_le_card ?_
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  calc
    Nat.choose N k = ∏ p ∈ Finset.range (N + 1), f p := by
      rw [Nat.prod_pow_factorization_choose N k hkn]
    _ = ∏ p ∈ s, f p := hprod_eq
    _ ≤ ∏ _p ∈ s, N := by
      refine Finset.prod_le_prod' ?_
      intro p hp
      exact Nat.pow_factorization_choose_le hN
    _ = N ^ s.card := by
      rw [Finset.prod_const]
    _ ≤ N ^ (k + 1).primesBelow.card := Nat.pow_le_pow_right hN hs_card

