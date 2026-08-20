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

theorem three_mul_piCount_le (k : ℕ) : 3 * piCount k ≤ k + 9 := by
  by_cases hk : k ≤ 27
  · interval_cases k <;> decide
  · -- For k > 27, we bound piCount by considering primes ≤ 3 and primes > 3
    -- Primes > 3 must be coprime to 6
    have h1 : piCount k = #{p ∈ Finset.range (k + 1) | p.Prime} := rfl
    let S := {p ∈ Finset.range (k + 1) | p.Prime}
    let A := {p ∈ Finset.range 4 | p.Prime}
    let B := {p ∈ Finset.Ico 4 (k + 1) | Nat.Coprime p 6}
    have hsub : S ⊆ A ∪ B := by
      intro x hx
      simp only [S, A, B, Finset.mem_union, Finset.mem_filter] at hx ⊢
      have hxrange := hx.1
      have hxprime := hx.2
      by_cases hx3 : x < 4
      · left; simp [hx3]; exact hxprime
      · right
        have hxrange' : x < k + 1 := Finset.mem_range.mp hxrange
        have hxIco : x ∈ Finset.Ico 4 (k + 1) := Finset.mem_Ico.mpr ⟨by omega, hxrange'⟩
        have hcop : x.Coprime 6 := by
          rw [Nat.Prime.coprime_iff_not_dvd hxprime]
          exact fun h => by have := Nat.le_of_dvd (by omega) h; interval_cases x <;> trivial
        exact ⟨hxIco, hcop⟩
    have hcard : #S ≤ #A + #B := le_trans (Finset.card_le_card hsub) (Finset.card_union_le A B)
    -- #A = 2 (primes 2 and 3)
    have hA : #A = 2 := by decide
    -- #B ≤ (k + 2) / 3
    have hB : #B ≤ (k + 2) / 3 := by
      -- B ⊆ {n ∈ Ico 4 (k+1) | n % 6 = 1 ∨ n % 6 = 5}
      let C := {n ∈ Finset.Ico 4 (k + 1) | n % 6 = 1 ∨ n % 6 = 5}
      have hBC : B ⊆ C := by
        intro n hn
        simp only [B, C, Finset.mem_filter] at hn ⊢
        refine ⟨hn.1, ?_⟩
        have hc := hn.2
        rw [Nat.Coprime, Nat.gcd_comm] at hc
        have hlt : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
        have hcases :
            n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
          omega
        rcases hcases with hm | hm | hm | hm | hm | hm <;> simp [hm]
        -- Case n % 6 = 0: then 6 | n, so gcd 6 n = 6
        · have := Nat.dvd_of_mod_eq_zero hm; rw [Nat.gcd_eq_left this] at hc; norm_num at hc
        -- Case n % 6 = 2: then 2 | n, so gcd 6 n ≥ 2
        · have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega : n % 2 = 0)
          exact absurd hc (by have := Nat.dvd_gcd (by norm_num : 2 ∣ 6) h2; omega)
        -- Case n % 6 = 3: then 3 | n, so gcd 6 n ≥ 3
        · have h3 : 3 ∣ n := Nat.dvd_of_mod_eq_zero (by omega : n % 3 = 0)
          exact absurd hc (by have := Nat.dvd_gcd (by norm_num : 3 ∣ 6) h3; omega)
        -- Case n % 6 = 4: then 2 | n, so gcd 6 n ≥ 2
        · have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero (by omega : n % 2 = 0)
          exact absurd hc (by have := Nat.dvd_gcd (by norm_num : 2 ∣ 6) h2; omega)
      -- #B ≤ #C, and #C can be bounded by counting elements with n % 6 = 1 or 5
      have hB_le_C : #B ≤ #C := Finset.card_le_card hBC
      -- C is a subset of Ico 4 (k+1), so #C ≤ k-3
      -- More precisely, #C = #{n ∈ Ico 4 (k+1) | n % 6 = 1 ∨ n % 6 = 5}
      -- We can partition by n / 6 and show there are at most 2 values per block of 6
      calc #B ≤ #C := hB_le_C
        _ = #{n ∈ Finset.Ico 4 (k + 1) | n % 6 = 1 ∨ n % 6 = 5} := rfl
        _ ≤ (k + 2) / 3 := by
          -- For any n, n % 6 ∈ {0, 1, 2, 3, 4, 5}, and exactly 2/6 = 1/3 satisfy = 1 or = 5
          -- We can bound by noting the set is contained in the image of a smaller set
          -- Define f : n ↦ (n / 3) for n with n % 6 ∈ {1, 5}
          -- f(1) = 0, f(5) = 1, f(7) = 2, f(11) = 3, f(13) = 4, ...
          -- This is injective and maps to [0, k/3]
          -- We use that n % 6 ∈ {1, 5} means n = 6q + 1 (q ≥ 1) or n = 6q + 5 (q ≥ 0)
          -- The count is floor((k-1)/6) + floor((k-5)/6) + 1 ≤ k/3
          have hbound : ∀ n, n ∈ {n ∈ Finset.Ico 4 (k + 1) | n % 6 = 1 ∨ n % 6 = 5} →
              n / 6 < (k + 2) / 3 := by
            intro n hn
            simp only [Finset.mem_filter, Finset.mem_Ico] at hn
            omega
          let s := {n ∈ Finset.Ico 4 (k + 1) | n % 6 = 1 ∨ n % 6 = 5}
          -- Map: 6q+1 → 2q, 6q+5 → 2q+1. This is injective.
          let f : ℕ → ℕ := fun n => 2 * (n / 6) + (n % 6 - 1) / 4
          have hfbound : ∀ n, n ∈ s → f n < (k + 2) / 3 := by
            intro n hn
            simp only [s, Finset.mem_filter, Finset.mem_Ico] at hn
            rcases hn.2 with hn1 | hn5 <;> simp [f] <;> omega
          have hf_inj : ∀ n m, n ∈ s → m ∈ s → f n = f m → n = m := by
            intro n m hn hm heq
            simp only [s, Finset.mem_filter, Finset.mem_Ico] at hn hm
            -- For n % 6 = 1: f n = 2*(n/6), for n % 6 = 5: f n = 2*(n/6) + 1
            rcases hn.2 with hn1 | hn5 <;> rcases hm.2 with hm1 | hm5 <;> simp [f] at heq <;> omega
          have himage : s.image f ⊆ Finset.range ((k + 2) / 3) := by
            intro x hx
            simp only [Finset.mem_image] at hx
            obtain ⟨n, hn, rfl⟩ := hx
            exact Finset.mem_range.mpr (hfbound n hn)
          have hinjOn : Set.InjOn f (s : Set ℕ) := by
            intro a ha b hb hab
            exact hf_inj a b ha hb hab
          have hcard_le : s.card ≤ (s.image f).card := by
            rw [Finset.card_image_of_injOn hinjOn]
          calc s.card ≤ (s.image f).card := hcard_le
            _ ≤ (Finset.range ((k + 2) / 3)).card := Finset.card_le_card himage
            _ = (k + 2) / 3 := Finset.card_range _
    -- Now combine: 3 * piCount k ≤ 3 * (#A + #B) ≤ 3 * (2 + (k+2)/3) ≤ k + 9
    have hfinal : 3 * piCount k ≤ k + 9 := by
      rw [h1]
      calc 3 * #S ≤ 3 * (#A + #B) := by omega
        _ = 3 * #A + 3 * #B := by ring
        _ ≤ 3 * #A + 3 * ((k + 2) / 3) := by gcongr
        _ = 3 * 2 + 3 * ((k + 2) / 3) := by rw [hA]
        _ ≤ k + 9 := by omega
    exact hfinal

/-! ### Upper bounds for the binomial coefficient -/

/-- If all prime factors of `N.choose k` are at most `k`, then `N.choose k ≤ N ^ π(k)`. -/
