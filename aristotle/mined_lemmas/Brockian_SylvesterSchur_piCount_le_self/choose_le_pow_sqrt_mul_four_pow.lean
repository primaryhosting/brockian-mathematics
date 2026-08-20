import Mathlib
namespace Brockian.SylvesterSchur

/-!
# The Sylvester–Schur theorem

If `n > k ≥ 1` then one of `n+1, …, n+k` has a prime factor `> k`.

The proof follows Erdős' argument: assuming the contrary, every prime factor of the
binomial coefficient `(n+k).choose k` is at most `k`.  This yields two upper bounds for
that binomial coefficient (one via the number of primes `≤ k`, one via the primorial),
both of which are contradicted by an elementary lower bound, except in a range of small
parameters which is covered by an explicit chain of primes.
-/

open Finset Real

/-! ### An elementary upper bound for the prime counting function -/

/-- The number of primes `≤ k`. -/

theorem choose_le_pow_sqrt_mul_four_pow {N k : ℕ} (hk : 26 ≤ k) (hkN : 2 * k + 1 ≤ N)
    (H : ∀ p : ℕ, p.Prime → p ∣ N.choose k → p ≤ k) :
    N.choose k ≤ N ^ Nat.sqrt N * 4 ^ min k (N / 3) := by
  have hkN' : k ≤ N := by omega
  have hNpos : 0 < N := by omega
  set M := min k (N / 3) with hMdef
  set f : ℕ → ℕ := fun p => p ^ (N.choose k).factorization p with hfdef
  have hMk : M ≤ k := min_le_left _ _
  have hMN : M ≤ N := le_trans hMk hkN'
  have hvanish : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.range (M + 1) → f x = 1 := by
    intro x hx hx2
    rw [Finset.mem_range, Nat.lt_succ_iff] at hx
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hx2
    by_cases hp : x.Prime
    · rcases Nat.lt_or_ge k x with hxk | hxk
      · have hz : (N.choose k).factorization x = 0 := by
          by_contra hne
          have hdvd : x ∣ N.choose k := Nat.dvd_of_factorization_pos hne
          exact absurd (H x hp hdvd) (by omega)
        simp [hfdef, hz]
      · have h3x : N < 3 * x := by omega
        have hxne2 : x ≠ 2 := by omega
        have hz := Nat.factorization_choose_of_lt_three_mul hxne2 hxk (by omega : x ≤ N - k) h3x
        simp [hfdef, hz]
    · simp [hfdef, Nat.factorization_eq_zero_of_not_prime _ hp]
  have hsub : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro x hx
    simp only [Finset.mem_range] at *
    omega
  have key : N.choose k = ∏ p ∈ Finset.range (M + 1), f p := by
    rw [← Nat.prod_pow_factorization_choose N k hkN']
    exact (Finset.prod_subset hsub hvanish).symm
  set S := {p ∈ Finset.range (M + 1) | Nat.Prime p} with hSdef
  have hS : ∏ p ∈ S, f p = ∏ p ∈ Finset.range (M + 1), f p := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose! h
    simp [hfdef, Nat.factorization_eq_zero_of_not_prime _ h]
  rw [key, ← hS, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt N)]
  apply Nat.mul_le_mul
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ N)).trans ?_
    · exact Nat.pow_factorization_choose_le hNpos
    · rw [Finset.prod_const]
      refine Nat.pow_le_pow_right (by omega) ?_
      have hc : (Finset.Icc 1 (Nat.sqrt N)).card = Nat.sqrt N := by
        rw [Nat.card_Icc]; omega
      refine (Finset.card_le_card fun x hx => ?_).trans hc.le
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_four_pow M)
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (Nat.pow_le_pow_right (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
    · refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
      exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

/-! ### Lower bounds for the binomial coefficient -/

/-- The elementary bound `(N/k)^k ≤ N.choose k`. -/
