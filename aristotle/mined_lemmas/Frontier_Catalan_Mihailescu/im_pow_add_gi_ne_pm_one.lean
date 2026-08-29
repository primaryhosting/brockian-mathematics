import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-- The full Catalan–Mihăilescu statement: `8` and `9` are the only consecutive
perfect powers, i.e. the only solution of `x ^ p = y ^ q + 1` in integers
`x, y, p, q > 1` is `3 ^ 2 = 2 ^ 3 + 1`. -/

theorem im_pow_add_gi_ne_pm_one {r : ℕ} (hodd : Odd r) (hr : 3 ≤ r) {a : ℤ}
    (ha : Even a) (ha0 : a ≠ 0) {d : ℤ} (hd : d = 1 ∨ d = -1) :
    (((a : GaussianInt) + gi) ^ r).im ≠ d := by
  intro hcon
  rw [im_pow_add_gi] at hcon
  set T : ℕ → ℤ := fun k => a ^ k * (r.choose k : ℤ) * eps (r - k) with hTdef
  obtain ⟨v, m, hm, hvm⟩ := Nat.exists_eq_two_pow_mul_odd (n := a.natAbs) (by simpa using ha0)
  obtain ⟨e, c, hc, hec⟩ :=
    Nat.exists_eq_two_pow_mul_odd (Nat.choose_ne_zero_iff.mpr (show 2 ≤ r by omega))
  have hv1 : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with h0 | h
    · exfalso
      rw [h0, pow_zero, one_mul] at hvm
      have hev : Even a.natAbs := Int.natAbs_even.mpr ha
      rw [hvm] at hev
      exact (Nat.not_odd_iff_even.mpr hev) hm
    · exact h
  have h2v : ((2:ℤ)) ^ v ∣ a := by
    have h1 : (2 ^ v : ℕ) ∣ a.natAbs := ⟨m, hvm⟩
    have h2 : ((2 ^ v : ℕ) : ℤ) ∣ ((a.natAbs : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h1
    push_cast at h2
    exact dvd_trans h2 ((abs_dvd a a).mpr dvd_rfl)
  -- split off the terms of index `0`, `1`, `2`
  have hsplit : ∑ k ∈ Finset.range (r + 1), T k
      = T 0 + T 1 + T 2 + ∑ k ∈ Finset.Ico 3 (r + 1), T k := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    ring
  have hT0 : T 0 = eps r := by simp [hTdef]
  have hT1 : T 1 = 0 := by
    have h1 : Even (r - 1) := by
      obtain ⟨k, hk⟩ := hodd; subst hk; exact ⟨k, by omega⟩
    simp [hTdef, eps_of_even h1]
  -- all terms of index `≥ 2` are divisible by `4`
  have h4a : ∀ k : ℕ, 2 ≤ k → (4:ℤ) ∣ a ^ k := by
    intro k hk
    have h1 : (2:ℤ) ^ 2 ∣ a ^ 2 := pow_dvd_pow_of_dvd ha.two_dvd 2
    exact dvd_trans (by norm_num) (dvd_trans h1 (pow_dvd_pow a hk))
  have h4T : ∀ k : ℕ, 2 ≤ k → (4:ℤ) ∣ T k := by
    intro k hk
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (h4a k hk) _) _
  have h4tail : (4:ℤ) ∣ ∑ k ∈ Finset.Ico 3 (r + 1), T k :=
    Finset.dvd_sum (fun k hk => h4T k (by simp only [Finset.mem_Ico] at hk; omega))
  -- hence the constant term equals `d`, and the rest of the sum vanishes
  have hepsr := eps_eq_one_or_neg_one hodd
  have hrest : T 2 + ∑ k ∈ Finset.Ico 3 (r + 1), T k = d - eps r := by
    rw [hsplit, hT1, hT0] at hcon; linarith
  have h4rest : (4:ℤ) ∣ d - eps r := by
    rw [← hrest]; exact dvd_add (h4T 2 (by omega)) h4tail
  have hepsd : eps r = d := by
    obtain ⟨w, hw⟩ := h4rest
    rcases hepsr with h1 | h1 <;> rcases hd with h2 | h2 <;> rw [h1, h2] at hw ⊢ <;> omega
  have hzero : T 2 + ∑ k ∈ Finset.Ico 3 (r + 1), T k = 0 := by rw [hrest, hepsd]; ring
  -- the `2`-adic contradiction
  set N : ℕ := 2 * v + e + 1 with hN
  have hclaim2 : ∀ k ∈ Finset.Ico 3 (r + 1), ((2:ℤ) ^ N) ∣ T k := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    rcases Nat.even_or_odd k with hke | hko
    · obtain ⟨j, hj⟩ := hke
      have hj2 : 2 ≤ j := by omega
      have hk2j : k = 2 * j := by omega
      have hnat : 2 ^ N ∣ r.choose (2 * j) * 2 ^ (2 * j * v) :=
        pow_two_dvd_term hv1 hj2 ⟨c, hec⟩
      have hz : ((2:ℤ)) ^ N ∣ (r.choose (2 * j) : ℤ) * ((2:ℤ)) ^ (2 * j * v) := by
        have h := Int.natCast_dvd_natCast.mpr hnat
        push_cast at h
        exact h
      have hdvd_a : ((2:ℤ)) ^ (2 * j * v) ∣ a ^ (2 * j) := by
        have h1 : (((2:ℤ) ^ v)) ^ (2 * j) ∣ a ^ (2 * j) := pow_dvd_pow_of_dvd h2v _
        rwa [← pow_mul, show v * (2 * j) = 2 * j * v from by ring] at h1
      have hfin : ((2:ℤ)) ^ N ∣ a ^ (2 * j) * (r.choose (2 * j) : ℤ) := by
        have h2 : ((2:ℤ)) ^ N ∣ (r.choose (2 * j) : ℤ) * a ^ (2 * j) :=
          dvd_trans hz (mul_dvd_mul_left _ hdvd_a)
        rwa [mul_comm] at h2
      rw [hTdef, hk2j]
      exact Dvd.dvd.mul_right hfin _
    · have hre : Even (r - k) := Nat.Odd.sub_odd hodd hko
      rw [hTdef]
      simp [eps_of_even hre]
  have hdvdT2 : ((2:ℤ) ^ N) ∣ T 2 := by
    have h1 : ((2:ℤ) ^ N) ∣ ∑ k ∈ Finset.Ico 3 (r + 1), T k := Finset.dvd_sum hclaim2
    have h2 : T 2 = -(∑ k ∈ Finset.Ico 3 (r + 1), T k) := by linarith
    rw [h2]
    exact dvd_neg.mpr h1
  have hodd_rm2 : Odd (r - 2) := Nat.Odd.sub_even (by omega) hodd even_two
  have heps2 := eps_sq_of_odd hodd_rm2
  have ha2 : a ^ 2 = ((2:ℤ)) ^ (2 * v) * (m : ℤ) ^ 2 := by
    have h1 : ((a.natAbs : ℤ)) ^ 2 = a ^ 2 := Int.natAbs_sq a
    rw [← h1, hvm]; push_cast; ring
  have hT2val : T 2 * eps (r - 2) = ((2:ℤ)) ^ (2 * v + e) * ((m ^ 2 * c : ℕ) : ℤ) := by
    have h1 : T 2 * eps (r - 2) = a ^ 2 * (r.choose 2 : ℤ) := by
      rw [hTdef]
      simp only
      linear_combination (a ^ 2 * (r.choose 2 : ℤ)) * heps2
    rw [h1, ha2, hec]
    push_cast
    rw [pow_add]
    ring
  have hdvd : ((2:ℤ) ^ N) ∣ ((2:ℤ)) ^ (2 * v + e) * ((m ^ 2 * c : ℕ) : ℤ) := by
    rw [← hT2val]
    exact Dvd.dvd.mul_right hdvdT2 _
  rw [hN, pow_succ] at hdvd
  have h2dvd : (2:ℤ) ∣ ((m ^ 2 * c : ℕ) : ℤ) :=
    (mul_dvd_mul_iff_left (by positivity : ((2:ℤ)) ^ (2 * v + e) ≠ 0)).mp hdvd
  have h2n : 2 ∣ m ^ 2 * c := by exact_mod_cast h2dvd
  have hoddmc : Odd (m ^ 2 * c) := (hm.pow).mul hc
  rw [Nat.odd_iff] at hoddmc
  omega

/-! ## Lebesgue's theorem: `x ^ p = y ^ 2 + 1` has no solutions -/

