import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian

/-- The *Goldbach wheel condition of order 2* for a modulus `m`:
every even number `n` is congruent, modulo `m`, to a sum `a + b` of two natural numbers
that are both coprime to `m`.

This is the condition saying that the "wheel" of modulus `m` does not obstruct
Goldbach-type representations of even numbers as sums of two numbers coprime to `m`
(in particular, as sums of two primes not dividing `m`). -/

theorem goldbachWheelK2_of_pos {m : ℕ} (hm : 0 < m) : GoldbachWheelK2 m := by
  classical
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · refine ⟨1, m - 1, Nat.coprime_one_left m, ?_, ?_⟩
    · have h : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
      have hco : Nat.Coprime (m - 1) (m - 1 + 1) := by simp [Nat.Coprime]
      rwa [h] at hco
    · have h : 1 + (m - 1) = m := by omega
      simp [h]
  · have hn2 : 2 ≤ n := by rcases hn with ⟨t, ht⟩; omega
    set k := n - 1 with hkdef
    have hnk : n = k + 1 := by omega
    have hkodd : ¬ (2 ∣ k) := by rcases hn with ⟨t, ht⟩; omega
    set S := m.primeFactors.filter (fun p => ¬ p ∣ k) with hS
    set T := m.primeFactors.filter (fun p => p ∣ k) with hT
    set P := ∏ p ∈ S, p with hP
    set Q := ∏ p ∈ T, p with hQ
    have hPQ : Nat.Coprime P Q := by
      apply Nat.Coprime.prod_left
      intro p hp
      apply Nat.Coprime.prod_right
      intro q hq
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
      have hne : p ≠ q := by
        intro h; subst h
        exact (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2
      exact (Nat.coprime_primes hpp hqp).mpr hne
    obtain ⟨a, ha1, ha2⟩ := Nat.chineseRemainder hPQ 1 2
    -- the congruences satisfied by `a` modulo each prime factor of `m`
    have hmod : ∀ p : ℕ, p.Prime → p ∣ m →
        (¬ p ∣ k → a ≡ 1 [MOD p]) ∧ (p ∣ k → a ≡ 2 [MOD p]) := by
      intro p pp hpm
      have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨pp, hpm, by omega⟩
      refine ⟨fun hk => ha1.of_dvd ?_, fun hk => ha2.of_dvd ?_⟩
      · exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hmem, hk⟩)
      · exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨hmem, hk⟩)
    -- `a` is coprime to `m`
    have hane : ∀ p : ℕ, p.Prime → p ∣ m → ¬ p ∣ a := by
      intro p pp hpm hpa
      have hp2 : 2 ≤ p := pp.two_le
      have h0 : a % p = 0 := Nat.mod_eq_zero_of_dvd hpa
      by_cases hk : p ∣ k
      · have h := (hmod p pp hpm).2 hk
        have hpodd : p ≠ 2 := by rintro rfl; exact hkodd hk
        have h2 : (2 : ℕ) % p = 2 := Nat.mod_eq_of_lt (by omega)
        rw [Nat.ModEq, h0, h2] at h
        omega
      · have h := (hmod p pp hpm).1 hk
        have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt (by omega)
        rw [Nat.ModEq, h0, h1] at h
        omega
    -- the complementary summand
    have hale : a ≤ n + a * m := by
      have : a * 1 ≤ a * m := Nat.mul_le_mul_left a hm
      omega
    have hsum : a + (n + a * m - a) = n + a * m := by omega
    have hbne : ∀ p : ℕ, p.Prime → p ∣ m → ¬ p ∣ (n + a * m - a) := by
      intro p pp hpm hpb
      have hb0 : (n + a * m - a) ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr hpb
      have h1 : a + (n + a * m - a) ≡ a + 0 [MOD p] := Nat.ModEq.add_left a hb0
      have h2 : n + a * m ≡ n + 0 [MOD p] :=
        Nat.ModEq.add_left n ((Nat.modEq_zero_iff_dvd).mpr (Dvd.dvd.mul_left hpm a))
      rw [hsum] at h1
      have han : a ≡ n [MOD p] := by simpa using h1.symm.trans h2
      by_cases hk : p ∣ k
      · have ha2' := (hmod p pp hpm).2 hk
        have hk1 : n ≡ 1 [MOD p] := by
          rw [hnk]
          calc k + 1 ≡ 0 + 1 [MOD p] := Nat.ModEq.add_right 1 ((Nat.modEq_zero_iff_dvd).mpr hk)
            _ = 1 := by ring
        have h21 : (2 : ℕ) ≡ 1 [MOD p] := ha2'.symm.trans (han.trans hk1)
        have hd : p ∣ 1 := (Nat.modEq_iff_dvd' (by omega)).mp h21.symm
        exact pp.one_lt.ne' (Nat.dvd_one.mp hd)
      · have ha1' := (hmod p pp hpm).1 hk
        have hn1 : n ≡ 1 [MOD p] := (ha1'.symm.trans han).symm
        have hk0 : k ≡ 0 [MOD p] := by
          rw [hnk] at hn1
          exact Nat.ModEq.add_right_cancel' 1 (by simpa using hn1)
        exact hk ((Nat.modEq_zero_iff_dvd).mp hk0)
    exact ⟨a, n + a * m - a, coprime_of_no_common_prime hane, coprime_of_no_common_prime hbne,
      by rw [hsum, Nat.add_mul_mod_self_right]⟩

/-- **New wheel modulus 727**: `727` satisfies the Goldbach wheel condition of order 2. -/
