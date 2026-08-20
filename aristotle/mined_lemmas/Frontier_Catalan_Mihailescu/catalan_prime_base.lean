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

lemma catalan_prime_base {x p n r : ℕ} (hr : r.Prime) (hx : 1 < x) (hp : 1 < p) (hn : 1 < n)
    (h : x ^ p = r ^ n + 1) : x = 3 ∧ p = 2 ∧ r = 2 ∧ n = 3 := by
  rcases eq_or_ne r 2 with rfl | hr2
  · obtain ⟨h1, h2, h3⟩ := catalan_two_pow_add_one hx hp hn h
    exact ⟨h1, h2, rfl, h3⟩
  exfalso
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  obtain ⟨c, rfl⟩ : ∃ c, x = c + 1 := ⟨x - 1, by omega⟩
  have hc1 : 1 ≤ c := by omega
  have hgeom := geom_nat c p
  set S := ∑ i ∈ Finset.range p, (c + 1) ^ i with hS
  have hprod : S * c = r ^ n := by omega
  have hcdvd : c ∣ r ^ n := ⟨S, by rw [← hprod]; ring⟩
  have hSdvd : S ∣ r ^ n := ⟨c, hprod.symm⟩
  obtain ⟨t, ht, hct⟩ := (Nat.dvd_prime_pow hr).1 hcdvd
  -- the base `x` cannot be `2`
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h'
    · exfalso
      have hc : c = 1 := by simpa using hct
      subst hc
      exact catalan_two_pow_sub_one (show 1 < r by omega) hp hn (by simpa using h)
    · exact h'
  have hrc : r ∣ c := hct ▸ dvd_pow_self r (by omega)
  -- the geometric sum is `≡ p (mod r)`, hence `r ∣ p`
  have hSmod : S % r = p % r := by
    rw [hS, Finset.sum_nat_mod]
    have hone : ∀ i ∈ Finset.range p, (c + 1) ^ i % r = 1 := by
      intro i _
      rw [Nat.pow_mod]
      have hc1r : (c + 1) % r = 1 := by
        obtain ⟨e, he⟩ := hrc
        subst he
        rw [Nat.mul_add_mod]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hc1r, one_pow]
      exact Nat.mod_eq_of_lt (by omega)
    rw [Finset.sum_congr rfl hone]
    simp
  have hSbig : 1 < S := by
    have hle : ∑ i ∈ Finset.range 2, (c + 1) ^ i ≤ S := by
      rw [hS]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset.mpr (by intro i hi; simp; omega))
    simp [Finset.sum_range_succ] at hle
    omega
  obtain ⟨u, hu, hSu⟩ := (Nat.dvd_prime_pow hr).1 hSdvd
  have hrS : r ∣ S := by
    rcases Nat.eq_zero_or_pos u with rfl | h'
    · simp at hSu; omega
    · exact hSu ▸ dvd_pow_self r (by omega)
  have hrp : r ∣ p := by
    have hp0 : p % r = 0 := by rw [← hSmod]; exact Nat.mod_eq_zero_of_dvd hrS
    exact Nat.dvd_of_mod_eq_zero hp0
  obtain ⟨p', rfl⟩ := hrp
  have hp'1 : 1 ≤ p' := by
    rcases Nat.eq_zero_or_pos p' with rfl | h'
    · simp at hp
    · exact h'
  -- second stage: `X ^ r = r ^ n + 1` with `X ≡ 1 (mod r)`
  set X := (c + 1) ^ p' with hX
  have hXr : X ^ r = r ^ n + 1 := by rw [hX, ← pow_mul, mul_comm p' r]; exact h
  have hXbig : r + 1 ≤ X := by
    have h1 : c + 1 ≤ X := by
      rw [hX]
      calc c + 1 = (c + 1) ^ 1 := (pow_one _).symm
      _ ≤ (c + 1) ^ p' := Nat.pow_le_pow_right (by omega) hp'1
    have h2 : r ≤ c := Nat.le_of_dvd (by omega) hrc
    omega
  obtain ⟨d, hXd⟩ : ∃ d, X = 1 + d := ⟨X - 1, by omega⟩
  have hdr : r ≤ d := by omega
  have hgeom2 := geom_nat d r
  set T := ∑ i ∈ Finset.range r, (1 + d) ^ i with hT
  have hT' : (∑ i ∈ Finset.range r, (d + 1) ^ i) = T := by
    rw [hT]; exact Finset.sum_congr rfl (fun i _ => by rw [add_comm])
  rw [hT'] at hgeom2
  have hXeq : (d + 1) ^ r = r ^ n + 1 := by rw [add_comm d 1, ← hXd]; exact hXr
  have hprod2 : T * d = r ^ n := by omega
  have hddvd : d ∣ r ^ n := ⟨T, by rw [← hprod2]; ring⟩
  have hTdvd : T ∣ r ^ n := ⟨d, hprod2.symm⟩
  obtain ⟨t', ht', hdt⟩ := (Nat.dvd_prime_pow hr).1 hddvd
  have hrd : r ∣ d := by
    rcases Nat.eq_zero_or_pos t' with rfl | h'
    · simp at hdt; omega
    · exact hdt ▸ dvd_pow_self r (by omega)
  have hTbig : r < T := by
    have h1 : ∑ i ∈ Finset.range 2, (1 + d) ^ i ≤ T := by
      rw [hT]
      exact Finset.sum_le_sum_of_subset (Finset.range_subset.mpr (by intro i hi; simp; omega))
    simp [Finset.sum_range_succ] at h1
    omega
  obtain ⟨u', hu', hTu⟩ := (Nat.dvd_prime_pow hr).1 hTdvd
  have hu'2 : 2 ≤ u' := by
    rcases Nat.lt_or_ge u' 2 with hlt | hge
    · interval_cases u' <;> simp at hTu <;> omega
    · exact hge
  have hr2T : r * r ∣ T := by
    have hpp : r ^ 2 ∣ r ^ u' := pow_dvd_pow r hu'2
    rw [← hTu] at hpp
    simpa [pow_two] using hpp
  -- but the geometric sum is exactly `r` modulo `r ^ 2`
  obtain ⟨K, hK⟩ := geom_sum_expand d r
  rw [← hT] at hK
  obtain ⟨e, he⟩ := hrd
  obtain ⟨f, hf⟩ := hr2T
  subst he
  rw [hf] at hK
  have key : r * (2 * r * f) = r * (2 + ((r - 1) * r * e + K * r * e * e)) := by
    ring_nf
    ring_nf at hK
    linarith [hK]
  have key2 : 2 * r * f = 2 + ((r - 1) * r * e + K * r * e * e) :=
    Nat.eq_of_mul_eq_mul_left (by omega) key
  have hd1 : r ∣ 2 * r * f := ⟨2 * f, by ring⟩
  have hd2 : r ∣ ((r - 1) * r * e + K * r * e * e) := ⟨(r - 1) * e + K * e * e, by ring⟩
  have hrdvd2 : r ∣ 2 := by
    have hsub := Nat.dvd_sub hd1 hd2
    simpa [show 2 * r * f - ((r - 1) * r * e + K * r * e * e) = 2 from by omega] using hsub
  have := Nat.le_of_dvd (by omega) hrdvd2
  omega

/-- **Catalan's equation when the smaller base is a prime power.**  The only solution is
`3 ^ 2 - 2 ^ 3 = 1`. -/
