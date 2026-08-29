import Mathlib
/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

/-- A *Catalan solution*: a pair of consecutive perfect powers, i.e. natural numbers with
`x ^ p = y ^ q + 1`, all of `x, y, p, q` being at least `2`. -/

theorem catalan_solution_of_rhs_base_two {x p q : ℕ} (h : IsCatalanSolution x p 2 q) :
    x = 3 ∧ p = 2 ∧ q = 3 := by
  obtain ⟨hx, hp, -, hq, heq⟩ := h
  have h2q : (2 : ℕ) ∣ 2 ^ q := dvd_pow_self 2 (by omega)
  have hxodd : ¬ (2 ∣ x) := by
    intro hdvd
    have : (2 : ℕ) ∣ x ^ p := dvd_pow hdvd (by omega)
    omega
  have hx3 : 3 ≤ x := by omega
  rcases Nat.even_or_odd p with hpe | hpo
  · obtain ⟨t, ht⟩ := hpe
    have ht1 : 1 ≤ t := by omega
    have hz : x ^ p = (x ^ t) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    set z := x ^ t with hzdef
    have hz3 : 3 ≤ z := by
      calc 3 ≤ x := hx3
        _ = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ t := Nat.pow_le_pow_right (by omega) ht1
    obtain ⟨w, hw⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
    have hw2 : 2 ≤ w := by omega
    have hzeq : z ^ 2 = 2 ^ q + 1 := by rw [← hz]; exact heq
    have hfac : w * (w + 2) = 2 ^ q := by
      have : (w + 1) ^ 2 = 2 ^ q + 1 := by rw [← hw]; exact hzeq
      nlinarith [this]
    have hdw : w ∣ 2 ^ q := ⟨w + 2, hfac.symm⟩
    have hdw2 : (w + 2) ∣ 2 ^ q := ⟨w, by rw [← hfac]; ring⟩
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdw
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdw2
    have ha1 : 1 ≤ a := by
      by_contra hc
      have : a = 0 := by omega
      subst this
      simp at ha
      omega
    have hwval : w = 2 := by
      by_contra hne
      have ha2 : 2 ≤ a := by
        rcases Nat.lt_or_ge a 2 with h | h
        · have ha1' : a = 1 := by omega
          rw [ha1', pow_one] at ha
          omega
        · exact h
      have h4a : (4 : ℕ) ∣ 2 ^ a := by
        have : (2 : ℕ) ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 ha2
        simpa using this
      have hb3 : 3 ≤ b := by
        by_contra hc
        interval_cases b <;> omega
      have h4b : (4 : ℕ) ∣ 2 ^ b := by
        have : (2 : ℕ) ^ 2 ∣ 2 ^ b := pow_dvd_pow 2 (by omega)
        simpa using this
      omega
    have hq3 : q = 3 := by
      have h8 : (2 : ℕ) ^ q = 2 ^ 3 := by rw [← hfac, hwval]; norm_num
      exact Nat.pow_right_injective (le_refl 2) h8
    have hzval : z = 3 := by omega
    have ht' : t = 1 := by
      by_contra hne
      have ht2 : 2 ≤ t := by omega
      have : x ^ 2 ≤ x ^ t := Nat.pow_le_pow_right (by omega) ht2
      have hx9 : 9 ≤ x ^ 2 := by nlinarith [hx3]
      omega
    refine ⟨?_, by omega, hq3⟩
    have hx1 : x ^ 1 = 3 := by rw [← ht']; exact hzval
    rwa [pow_one] at hx1
  · exfalso
    have hp3 : 3 ≤ p := by
      rcases hpo with ⟨t, ht⟩; omega
    exact odd_pow_sub_one_ne_two_pow hx3 hp3 hpo heq

/-- In any solution of Catalan's equation the exponents are coprime; in particular there is
no solution with equal exponents. -/
