import Mathlib
import NTGaps2.ThreeSquares

namespace MS2.NTG2

/-- As stated by the user this theorem has conclusion `True`, so the hypotheses `hp` and `h5`
are not needed. A genuine statement in this direction is `wolstenholme_weak'` below. -/

theorem exists_ternary_data (n : ℕ) (hn : 0 < n) (h4 : ¬ (4 ∣ n)) (h8 : n % 8 ≠ 7) :
    ∃ u M s : ℤ, 0 < M ∧ (n : ℤ) * (u * M - s ^ 2) - M = 1 := by
  have hcases : n % 4 = 1 ∨ n % 8 = 3 ∨ n % 8 = 2 ∨ n % 8 = 6 := by omega
  rcases hcases with hn4 | hn8 | hn2 | hn6
  · -- `n ≡ 1 mod 4`: take `p ≡ 2n-1 mod 4n`, so `p ≡ 1 mod 4` and `n ∣ p+1`
    set r := 2 * n - 1 with hr
    have hrsucc : n ∣ r + 1 := ⟨2, by omega⟩
    have hcop : Nat.Coprime r (4 * n) :=
      Nat.Coprime.mul_right (by simpa using coprime_two_pow_of_odd (by omega) 2)
        (coprime_of_dvd_succ hrsucc)
    obtain ⟨p, -, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 4 (q := 4 * n) (a := r) (by omega) hcop
    haveI : Fact p.Prime := ⟨hp⟩
    have hp4 : p % 4 = 1 := by
      have h := Nat.ModEq.of_dvd (⟨n, rfl⟩ : (4 : ℕ) ∣ 4 * n) hpmod
      unfold Nat.ModEq at h
      omega
    have hdvd : n ∣ p + 1 := dvd_succ_of_modEq ⟨4, by ring⟩ hpmod hrsucc
    exact data_of_prime n p hdvd (symbol_one_mod_four n p hn4 hp4 hdvd)
  · -- `n ≡ 3 mod 8`: take `p ≡ (n-1)/2 mod 2n`, so `n ∣ 2p+1`
    obtain ⟨t, ht⟩ : ∃ t, n = 8 * t + 3 := ⟨n / 8, by omega⟩
    set r := 4 * t + 1 with hr
    have hrsucc : n ∣ 2 * r + 1 := ⟨1, by omega⟩
    have hcop : Nat.Coprime r (2 * n) :=
      Nat.Coprime.mul_right (by simpa using coprime_two_pow_of_odd (by omega) 1)
        (coprime_of_dvd_two_succ hrsucc)
    obtain ⟨p, -, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 4 (q := 2 * n) (a := r) (by omega) hcop
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p % 2 = 1 := by
      have h := Nat.ModEq.of_dvd (⟨n, rfl⟩ : (2 : ℕ) ∣ 2 * n) hpmod
      unfold Nat.ModEq at h
      omega
    have hdvd : n ∣ 2 * p + 1 := dvd_two_succ_of_modEq ⟨2, by ring⟩ hpmod hrsucc
    exact data_of_prime_two n p hp2 hdvd (symbol_three_mod_eight n p hn8 hp2 hdvd)
  · -- `n ≡ 2 mod 8`: `n = 2n'` with `n' ≡ 1 mod 4`; take `p ≡ 1 mod 8`, `p ≡ -1 mod n'`
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * (2 * m + 1) := ⟨n / 4, by omega⟩
    set n' := 2 * m + 1 with hn'
    have hn'4 : n' % 4 = 1 := by omega
    set r := 8 * (m ^ 2 + m) + 1 with hr
    have hrsucc : n' ∣ r + 1 := ⟨2 * n', by rw [hr, hn']; ring⟩
    have hcop : Nat.Coprime r (8 * n') :=
      Nat.Coprime.mul_right (by simpa using coprime_two_pow_of_odd (by omega) 3)
        (coprime_of_dvd_succ hrsucc)
    obtain ⟨p, -, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 4 (q := 8 * n') (a := r) (by omega) hcop
    haveI : Fact p.Prime := ⟨hp⟩
    have hp8 : p % 8 = 1 := by
      have h := Nat.ModEq.of_dvd (⟨n', rfl⟩ : (8 : ℕ) ∣ 8 * n') hpmod
      unfold Nat.ModEq at h
      omega
    have hdvd' : n' ∣ p + 1 := dvd_succ_of_modEq ⟨8, by ring⟩ hpmod hrsucc
    have hdvd : n ∣ p + 1 := by
      rw [hm]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ hdvd'
      · exact (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
      · omega
    have hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1 := by
      have h1 : legendreSym p (-1) = 1 := by
        rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_one_mod_four (by omega)]
      have hcast : (n : ℤ) = 2 * (n' : ℤ) := by rw [hm]; push_cast; ring
      have h2 := symbol_even n' p (Nat.odd_iff.mpr (by omega)) (by omega) hdvd'
      have hchi8 : ZMod.χ₈ (p : ℕ) = 1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        have e1 : p % 2 ≠ 0 := by omega
        have e2 : p % 8 = 1 ∨ p % 8 = 7 := by omega
        simp [e1, e2]
      rw [h1, one_mul, hcast, h2, hchi8, ZMod.χ₄_nat_one_mod_four hn'4, one_mul]
    exact data_of_prime n p hdvd hsign
  · -- `n ≡ 6 mod 8`: `n = 2n'` with `n' ≡ 3 mod 4`; take `p ≡ 5 mod 8`, `p ≡ -1 mod n'`
    obtain ⟨m, hm⟩ : ∃ m, n = 2 * (2 * m + 1) := ⟨n / 4, by omega⟩
    set n' := 2 * m + 1 with hn'
    have hn'4 : n' % 4 = 3 := by omega
    set r := 24 * (m ^ 2 + m) + 5 with hr
    have hrsucc : n' ∣ r + 1 := ⟨6 * n', by rw [hr, hn']; ring⟩
    have hcop : Nat.Coprime r (8 * n') :=
      Nat.Coprime.mul_right (by simpa using coprime_two_pow_of_odd (by omega) 3)
        (coprime_of_dvd_succ hrsucc)
    obtain ⟨p, -, hp, hpmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq 4 (q := 8 * n') (a := r) (by omega) hcop
    haveI : Fact p.Prime := ⟨hp⟩
    have hp8 : p % 8 = 5 := by
      have h := Nat.ModEq.of_dvd (⟨n', rfl⟩ : (8 : ℕ) ∣ 8 * n') hpmod
      unfold Nat.ModEq at h
      omega
    have hdvd' : n' ∣ p + 1 := dvd_succ_of_modEq ⟨8, by ring⟩ hpmod hrsucc
    have hdvd : n ∣ p + 1 := by
      rw [hm]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ hdvd'
      · exact (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
      · omega
    have hsign : legendreSym p (-1) * legendreSym p (n : ℤ) = 1 := by
      have h1 : legendreSym p (-1) = 1 := by
        rw [legendreSym.at_neg_one (by omega), ZMod.χ₄_nat_one_mod_four (by omega)]
      have hcast : (n : ℤ) = 2 * (n' : ℤ) := by rw [hm]; push_cast; ring
      have h2 := symbol_even n' p (Nat.odd_iff.mpr (by omega)) (by omega) hdvd'
      have hchi8 : ZMod.χ₈ (p : ℕ) = -1 := by
        rw [ZMod.χ₈_nat_eq_if_mod_eight]
        have e1 : p % 2 ≠ 0 := by omega
        have e2 : ¬ (p % 8 = 1 ∨ p % 8 = 7) := by omega
        simp [e1, e2]
      rw [h1, one_mul, hcast, h2, hchi8, ZMod.χ₄_nat_three_mod_four hn'4]
      ring
    exact data_of_prime n p hdvd hsign

end ThreeSquares

import NTGaps2.BinaryForm

/-!
# Positive definite integral ternary quadratic forms of determinant one

The main result of this file is `ThreeSquares.ternary_sum_three_squares`: every value of a
positive definite integral ternary quadratic form (in the classical "integral matrix" sense)
of determinant `1` is a sum of three squares.

The proof is the classical reduction argument: the minimum `a` of the form satisfies
`27 a³ ≤ 64` by Lagrange's bound applied to the binary form obtained by completing the square,
hence `a = 1`; completing the square then exhibits the form as a sum of three squares of
integral linear forms.
-/

namespace ThreeSquares

open Matrix

/-- The quadratic form attached to a symmetric integer matrix. -/
