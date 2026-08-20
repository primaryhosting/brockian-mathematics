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

lemma catalan_stage_one {y q r m : ℕ} (hr : r.Prime) (hr3 : 3 ≤ r) (hy : 1 < y) (hq : 1 < q)
    (hqodd : Odd q) (h : r ^ m = y ^ q + 1) : r ∣ q := by
  have hZ : ((r:ℤ)) ^ m = (y:ℤ) ^ q + 1 := by exact_mod_cast h
  set Y : ℤ := (y : ℤ) with hYdef
  have hY2 : 2 ≤ Y := by rw [hYdef]; exact_mod_cast hy
  set A : ℤ := ∑ i ∈ Finset.range q, (-Y) ^ i with hA
  have hAmul : A * (Y + 1) = (r:ℤ) ^ m := by rw [hA, neg_geom_mul Y hqodd, hZ]
  have hrpos : (0:ℤ) < (r:ℤ) ^ m := by positivity
  have hApos : 0 < A := by nlinarith [hAmul, hrpos]
  obtain ⟨u, hu, hAu⟩ := int_dvd_prime_pow hApos hr ⟨Y + 1, hAmul.symm⟩
  have hy1n : (y + 1) ∣ r ^ m := by
    have h1 : ((y:ℤ) + 1) ∣ (r:ℤ) ^ m := ⟨A, by linarith [hAmul]⟩
    have h2 : ((y + 1 : ℕ) : ℤ) ∣ ((r ^ m : ℕ) : ℤ) := by push_cast; exact h1
    exact_mod_cast h2
  obtain ⟨b, hb, hbeq⟩ := (Nat.dvd_prime_pow hr).1 hy1n
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | h'
    · simp at hbeq; omega
    · exact h'
  have hrY : (r:ℤ) ∣ Y + 1 := by
    have h1 : (r:ℕ) ∣ (y + 1) := hbeq ▸ dvd_pow_self r (by omega)
    have h2 : ((r:ℕ):ℤ) ∣ ((y + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h1
    push_cast at h2
    exact h2
  have hAq : (r:ℤ) ∣ A - (q:ℤ) := by
    have hsum : A - (q:ℤ) = ∑ i ∈ Finset.range q, ((-Y) ^ i - 1) := by
      rw [hA, Finset.sum_sub_distrib]
      simp
    rw [hsum]
    refine Finset.dvd_sum (fun i _ => ?_)
    have h1 : (-Y - 1) ∣ ((-Y) ^ i - 1 ^ i) := sub_dvd_pow_sub_pow (-Y) 1 i
    have h2 : (r:ℤ) ∣ (-Y - 1) := by
      obtain ⟨c, hc⟩ := hrY
      exact ⟨-c, by linarith [hc]⟩
    simpa using h2.trans h1
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with rfl | h'
    · exfalso
      simp at hAu
      rw [hAu, one_mul] at hAmul
      have hEq : Y ^ q = Y := by linarith [hZ, hAmul]
      have hgt : Y < Y ^ q := by
        calc Y = Y ^ 1 := (pow_one Y).symm
        _ < Y ^ q := by apply pow_lt_pow_right₀ (by linarith) (by omega)
      linarith
    · exact h'
  have hrA : (r:ℤ) ∣ A := hAu ▸ dvd_pow_self (r:ℤ) (by omega)
  have hrqZ : (r:ℤ) ∣ (q:ℤ) := by simpa using dvd_sub hrA hAq
  exact_mod_cast hrqZ

/-- Second stage: `r ^ m = z ^ r + 1` with `r` an odd prime forces `r = 3`, `z = 2`, `m = 2`. -/
