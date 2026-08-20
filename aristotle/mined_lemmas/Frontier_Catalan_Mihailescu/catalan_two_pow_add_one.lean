import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma catalan_two_pow_add_one {x p q : ℕ} (hx : 1 < x) (hp : 1 < p) (hq : 1 < q)
    (h : x ^ p = 2 ^ q + 1) : x = 3 ∧ p = 2 ∧ q = 3 := by
  have h2q : Even (2 ^ q) := (Nat.even_pow (n := q)).2 ⟨even_two, by omega⟩
  have hxodd : Odd x := by
    rcases Nat.even_or_odd x with he | ho
    · exfalso
      have : Even (x ^ p) := (Nat.even_pow (n := p)).2 ⟨he, by omega⟩
      rcases this with ⟨t, ht⟩; rcases h2q with ⟨s, hs⟩; omega
    · exact ho
  obtain ⟨c, hxc, hce⟩ : ∃ c, x = c + 1 ∧ Even c := by
    rcases hxodd with ⟨t, ht⟩; exact ⟨2 * t, by omega, ⟨t, by ring⟩⟩
  subst hxc
  have hc2 : 2 ≤ c := by rcases hce with ⟨t, ht⟩; omega
  have hcodd : Odd (c + 1) := by rcases hce with ⟨t, ht⟩; exact ⟨t, by omega⟩
  -- the exponent `p` must be even
  have hpeven : Even p := by
    rcases Nat.even_or_odd p with he | ho
    · exact he
    · exfalso
      have hkey := geom_nat c p
      set S := ∑ i ∈ Finset.range p, (c + 1) ^ i with hS
      have hSdvd : S ∣ 2 ^ q := ⟨c, by omega⟩
      have hSodd : Odd S := by
        have hmod : S % 2 = p % 2 := by
          rw [hS, Finset.sum_nat_mod]
          have hone : ∀ i ∈ Finset.range p, (c + 1) ^ i % 2 = 1 :=
            fun i _ => Nat.odd_iff.1 hcodd.pow
          rw [Finset.sum_congr rfl hone]
          simp
        rcases ho with ⟨t, ht⟩
        exact Nat.odd_iff.2 (by omega)
      obtain ⟨i, hi, hSi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hSdvd
      have hS1 : S = 1 := by
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · simpa using hSi
        · exfalso
          rw [hSi] at hSodd
          rcases hSodd with ⟨t, ht⟩
          have h2 : (2:ℕ) ∣ 2 ^ i := dvd_pow_self 2 hipos.ne'
          omega
      have hsubset : Finset.range 2 ⊆ Finset.range p :=
        Finset.range_subset.mpr (by intro i hi; simp; omega)
      have hsub : ∑ i ∈ Finset.range 2, (c + 1) ^ i ≤ S := by
        rw [hS]; exact Finset.sum_le_sum_of_subset hsubset
      simp [Finset.sum_range_succ] at hsub
      omega
  obtain ⟨m, rfl⟩ := hpeven
  set X := (c + 1) ^ m with hX
  have hX2 : X * X = 2 ^ q + 1 := by rw [hX, ← pow_add]; exact h
  have hXodd : Odd X := hcodd.pow
  have hX3 : 3 ≤ X := by
    rcases Nat.lt_or_ge X 3 with hlt | hge
    · exfalso
      have h4 : (4:ℕ) ≤ 2 ^ q := by
        calc (4:ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) (by omega)
      interval_cases X <;> omega
    · exact hge
  obtain ⟨d, hXd, hde⟩ : ∃ d, X = d + 1 ∧ Even d := by
    rcases hXodd with ⟨t, ht⟩; exact ⟨2 * t, by omega, ⟨t, by ring⟩⟩
  have hd2 : 2 ≤ d := by rcases hde with ⟨t, ht⟩; omega
  have hfac : d * (d + 2) = 2 ^ q := by rw [hXd] at hX2; nlinarith [hX2]
  obtain ⟨i, hi, hdi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (⟨d + 2, hfac.symm⟩ : d ∣ 2 ^ q)
  obtain ⟨j, hj, hdj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
    (⟨d, by rw [← hfac]; ring⟩ : (d + 2) ∣ 2 ^ q)
  have hd : d = 2 := by
    rcases Nat.lt_or_ge i 2 with hlt | hge
    · interval_cases i <;> omega
    · exfalso
      have h4i : (4:ℕ) ∣ 2 ^ i := by
        have : (2:ℕ) ^ 2 ∣ 2 ^ i := pow_dvd_pow 2 hge
        simpa using this
      have hj2 : j ≤ 1 := by
        by_contra hcon
        push_neg at hcon
        have h4j : (4:ℕ) ∣ 2 ^ j := by
          have : (2:ℕ) ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
          simpa using this
        rcases h4i with ⟨s, hs⟩; rcases h4j with ⟨t, ht⟩; omega
      interval_cases j <;> omega
  subst hd
  have hq3 : q = 3 := by
    have h8 : (2:ℕ) ^ q = 2 ^ 3 := by rw [← hfac]; norm_num
    exact Nat.pow_right_injective (by omega) h8
  have hX3' : X = 3 := by omega
  rw [hX] at hX3'
  have hm1 : m = 1 ∧ c + 1 = 3 := by
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp at hX3'
    · have hdvd : (c + 1) ∣ 3 := by
        rw [← hX3']
        exact dvd_pow_self _ hmpos.ne'
      have hc1 : c + 1 = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
        · omega
        · exact h1
      refine ⟨?_, hc1⟩
      rw [hc1] at hX3'
      have h3 : (3:ℕ) ^ m = 3 ^ 1 := by simpa using hX3'
      exact Nat.pow_right_injective (by omega) h3
  exact ⟨by omega, by omega, hq3⟩

/-- Catalan's equation when the larger power is a power of two: no solutions. -/
