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

lemma catalan_stage_two {z r m : ℕ} (hr : r.Prime) (hrodd : Odd r) (hr3 : 3 ≤ r) (hz : 2 ≤ z)
    (h : r ^ m = z ^ r + 1) : r = 3 ∧ z = 2 ∧ m = 2 := by
  have hZ : ((r:ℤ)) ^ m = (z:ℤ) ^ r + 1 := by exact_mod_cast h
  set Z : ℤ := (z : ℤ) with hZdef
  have hZ2 : 2 ≤ Z := by rw [hZdef]; exact_mod_cast hz
  set A : ℤ := ∑ i ∈ Finset.range r, (-Z) ^ i with hA
  have hAmul : A * (Z + 1) = (r:ℤ) ^ m := by rw [hA, neg_geom_mul Z hrodd, hZ]
  have hrpos : (0:ℤ) < (r:ℤ) ^ m := by positivity
  have hApos : 0 < A := by nlinarith [hAmul, hrpos]
  obtain ⟨u, hu, hAu⟩ := int_dvd_prime_pow hApos hr ⟨Z + 1, hAmul.symm⟩
  have hz1n : (z + 1) ∣ r ^ m := by
    have h1 : ((z:ℤ) + 1) ∣ (r:ℤ) ^ m := ⟨A, by linarith [hAmul]⟩
    have h2 : ((z + 1 : ℕ) : ℤ) ∣ ((r ^ m : ℕ) : ℤ) := by push_cast; exact h1
    exact_mod_cast h2
  obtain ⟨b, hb, hbeq⟩ := (Nat.dvd_prime_pow hr).1 hz1n
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | h'
    · simp at hbeq; omega
    · exact h'
  have hrZ : (r:ℤ) ∣ Z + 1 := by
    have h1 : (r:ℕ) ∣ (z + 1) := hbeq ▸ dvd_pow_self r (by omega)
    have h2 : ((r:ℕ):ℤ) ∣ ((z + 1 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h1
    push_cast at h2
    exact h2
  obtain ⟨E, hE⟩ : ∃ E : ℤ, -Z - 1 = (r:ℤ) * E := by
    obtain ⟨c, hc⟩ := hrZ
    exact ⟨-c, by linarith [hc]⟩
  have hAsum : A = ∑ i ∈ Finset.range r, (1 + ((r:ℤ) * E)) ^ i := by
    rw [hA]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    linarith [hE]
  obtain ⟨K, hK⟩ := geom_sum_expand_int ((r:ℤ) * E) r
  rw [← hAsum] at hK
  have hrne : ((r:ℤ)) ≠ 0 := by positivity
  have hu1 : u ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, hc2⟩ : ((r:ℤ)) ^ 2 ∣ A := by rw [hAu]; exact pow_dvd_pow _ (by omega)
    have e1 : 2 * ((r:ℤ) ^ 2 * c) = 2 * (r:ℤ) + (r:ℤ) * ((r:ℤ) - 1) * ((r:ℤ) * E)
        + K * ((r:ℤ) * E * ((r:ℤ) * E)) := by rw [← hc2]; exact hK
    have hkey : (r:ℤ) * ((r:ℤ) * (2 * c))
        = (r:ℤ) * (2 + (r:ℤ) * (((r:ℤ) - 1) * E + K * (E * E))) := by
      ring_nf; ring_nf at e1; linarith [e1]
    have hkey2 := mul_left_cancel₀ hrne hkey
    have hrd2 : (r:ℤ) ∣ 2 :=
      ⟨2 * c - (((r:ℤ) - 1) * E + K * (E * E)), by linarith [hkey2]⟩
    have hrn2 : (r:ℕ) ∣ 2 := by exact_mod_cast hrd2
    have := Nat.le_of_dvd (by omega) hrn2
    omega
  have hu0 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with rfl | h'
    · exfalso
      simp at hAu
      rw [hAu, one_mul] at hAmul
      have hEq : Z ^ r = Z := by linarith [hZ, hAmul]
      have hgt : Z < Z ^ r := by
        calc Z = Z ^ 1 := (pow_one Z).symm
        _ < Z ^ r := by apply pow_lt_pow_right₀ (by linarith) (by omega)
      linarith
    · exact h'
  have huu : u = 1 := by omega
  rw [huu, pow_one] at hAu
  have hfinal : z ^ r + 1 = r * (z + 1) := by
    have hcast : (z:ℤ) ^ r + 1 = (r:ℤ) * ((z:ℤ) + 1) := by rw [← hZ, ← hAmul, hAu]
    exact_mod_cast hcast
  obtain ⟨hr3', hz2⟩ := catalan_small_eq hz hr3 hfinal
  subst hr3'
  subst hz2
  refine ⟨rfl, rfl, ?_⟩
  have h9 : (3:ℕ) ^ m = 3 ^ 2 := by rw [h]; norm_num
  exact Nat.pow_right_injective (by omega) h9

/-- **Catalan's equation with a prime power on the larger side and odd `q`.** -/
