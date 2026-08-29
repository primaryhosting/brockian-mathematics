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
def IsCatalanSolution (x p y q : ℕ) : Prop :=
  2 ≤ x ∧ 2 ≤ p ∧ 2 ≤ y ∧ 2 ≤ q ∧ x ^ p = y ^ q + 1

/-- `9 = 3 ^ 2` and `8 = 2 ^ 3` are consecutive perfect powers. -/
theorem isCatalanSolution_nine_eight : IsCatalanSolution 3 2 2 3 :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The full statement of the Catalan–Mihăilescu theorem: `3 ^ 2 - 2 ^ 3 = 1` is the only
solution of `x ^ p - y ^ q = 1` in natural numbers `x, y, p, q ≥ 2`. -/
def CatalanMihailescuStatement : Prop :=
  ∀ x p y q : ℕ, IsCatalanSolution x p y q → (x, p, y, q) = (3, 2, 2, 3)

/-! ### Elementary auxiliary results -/

/-- For `b ≥ 1` and `n ≥ 2`, the `n`-th powers of `b` and `b + 1` differ by more than `1`. -/
lemma add_two_le_succ_pow {b n : ℕ} (hb : 1 ≤ b) (hn : 2 ≤ n) : b ^ n + 2 ≤ (b + 1) ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      · omega
      · have h1 : (b + 1) ^ (1 + 1) = b ^ (1 + 1) + 2 * b + 1 := by ring
        omega
    · have hih := ih h
      have hexp : (b + 1) ^ (n + 1) = (b + 1) * (b + 1) ^ n := by ring
      have hb' : b ^ (n + 1) = b * b ^ n := by ring
      nlinarith [pow_pos (show 0 < b by omega) n]

/-- Two `n`-th powers of positive numbers with `n ≥ 2` never differ by exactly `1`. -/
lemma pow_ne_pow_add_one {a b n : ℕ} (hb : 1 ≤ b) (hn : 2 ≤ n) : a ^ n ≠ b ^ n + 1 := by
  intro h
  have hab : b < a := by
    by_contra hc
    push_neg at hc
    have : a ^ n ≤ b ^ n := Nat.pow_le_pow_left hc n
    omega
  have h1 : (b + 1) ^ n ≤ a ^ n := Nat.pow_le_pow_left hab n
  have h2 := add_two_le_succ_pow hb hn
  omega

/-- A power of two cannot be congruent to a strictly smaller power of two modulo the next
power of two. -/
lemma not_modEq_pow_two {k n : ℕ} (hn : k + 1 ≤ n) : ¬ ((2 : ℕ) ^ n ≡ 2 ^ k [MOD 2 ^ (k + 1)]) := by
  intro h
  have hdvd : (2 : ℕ) ^ (k + 1) ∣ 2 ^ n := pow_dvd_pow 2 hn
  have h0 : 2 ^ n % 2 ^ (k + 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvd
  have hlt : (2 : ℕ) ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h1 : (2 : ℕ) ^ k % 2 ^ (k + 1) = 2 ^ k := Nat.mod_eq_of_lt hlt
  have hk : 0 < (2 : ℕ) ^ k := Nat.two_pow_pos k
  rw [Nat.ModEq, h0, h1] at h
  omega

/-- If `u ^ 2 ≡ 1` modulo `m`, then `u ^ e ≡ u` modulo `m` for every odd `e`. -/
lemma pow_odd_modEq_self {u m e : ℕ} (he : Odd e) (h : u ^ 2 ≡ 1 [MOD m]) :
    u ^ e ≡ u [MOD m] := by
  obtain ⟨t, rfl⟩ := he
  have hrw : u ^ (2 * t + 1) = (u ^ 2) ^ t * u := by ring
  rw [hrw]
  calc (u ^ 2) ^ t * u ≡ 1 ^ t * u [MOD m] := Nat.ModEq.mul (Nat.ModEq.pow t h) (Nat.ModEq.refl u)
    _ = u := by ring

/-- `u ^ m + 1` is never a power of two when `u ≥ 3` and `m ≥ 3` is odd. -/
lemma odd_pow_add_one_ne_two_pow {u m n : ℕ} (hu : 3 ≤ u) (hm : 3 ≤ m) (hodd : Odd m) :
    u ^ m + 1 ≠ 2 ^ n := by
  intro heq
  have hdvd : u + 1 ∣ u ^ m + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow u 1 hodd
    simpa using h
  rw [heq] at hdvd
  obtain ⟨k, hkn, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have huodd : Odd u := by
    rcases Nat.even_or_odd u with he | ho
    · exfalso
      obtain ⟨t, ht⟩ := he
      have hk1 : 1 ≤ k := by
        by_contra hc
        have : k = 0 := by omega
        subst this
        simp at hk
        omega
      have : (2 : ℕ) ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      omega
    · exact ho
  obtain ⟨d, hd⟩ := huodd
  have hkk : (2 : ℕ) ^ (k + 1) = 4 * (d + 1) := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have hsq : u ^ 2 ≡ 1 [MOD 2 ^ (k + 1)] := by
    have h1 : u ^ 2 = 2 ^ (k + 1) * d + 1 := by rw [hkk, hd]; ring
    calc u ^ 2 = 2 ^ (k + 1) * d + 1 := h1
      _ ≡ 0 + 1 [MOD 2 ^ (k + 1)] := Nat.ModEq.add_right 1 ((Nat.modEq_zero_iff_dvd).2 ⟨d, rfl⟩)
      _ = 1 := by ring
  have hpow : u ^ m ≡ u [MOD 2 ^ (k + 1)] := pow_odd_modEq_self hodd hsq
  have hfin : (2 : ℕ) ^ n ≡ 2 ^ k [MOD 2 ^ (k + 1)] := by
    calc (2 : ℕ) ^ n = u ^ m + 1 := heq.symm
      _ ≡ u + 1 [MOD 2 ^ (k + 1)] := Nat.ModEq.add_right 1 hpow
      _ = 2 ^ k := hk
  have hn : k + 1 ≤ n := by
    have h3 : u ^ 3 ≤ u ^ m := Nat.pow_le_pow_right (by omega) hm
    have h4 : (2 : ℕ) ^ (k + 1) < 2 ^ n := by
      have hu3 : u ^ 3 = u * u * u := by ring
      nlinarith [heq, hd]
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 h4
    omega
  exact not_modEq_pow_two hn hfin

/-- `u ^ m - 1` is never a power of two when `u ≥ 3` and `m ≥ 3` is odd. -/
lemma odd_pow_sub_one_ne_two_pow {u m n : ℕ} (hu : 3 ≤ u) (hm : 3 ≤ m) (hodd : Odd m) :
    u ^ m ≠ 2 ^ n + 1 := by
  intro heq
  have hdvd : u - 1 ∣ 2 ^ n := by
    have h := Nat.sub_dvd_pow_sub_pow u 1 m
    simp only [one_pow, heq, Nat.add_sub_cancel] at h
    exact h
  obtain ⟨k, hkn, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hk' : u = 2 ^ k + 1 := by omega
  have hk1 : 1 ≤ k := by
    by_contra hc
    have hk0 : k = 0 := by omega
    subst hk0
    simp at hk'
    omega
  obtain ⟨d, hd⟩ : ∃ d, (2 : ℕ) ^ k = 2 * d := ⟨2 ^ (k - 1), by
    rw [← pow_succ']
    congr 1
    omega⟩
  have hd1 : 1 ≤ d := by
    have := Nat.two_pow_pos k
    omega
  have hkk : (2 : ℕ) ^ (k + 1) = 4 * d := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  have hu2 : u = 2 * d + 1 := by omega
  have hsq : u ^ 2 ≡ 1 [MOD 2 ^ (k + 1)] := by
    have h1 : u ^ 2 = 2 ^ (k + 1) * (d + 1) + 1 := by rw [hkk, hu2]; ring
    calc u ^ 2 = 2 ^ (k + 1) * (d + 1) + 1 := h1
      _ ≡ 0 + 1 [MOD 2 ^ (k + 1)] := Nat.ModEq.add_right 1 ((Nat.modEq_zero_iff_dvd).2 ⟨d + 1, rfl⟩)
      _ = 1 := by ring
  have hpow : u ^ m ≡ u [MOD 2 ^ (k + 1)] := pow_odd_modEq_self hodd hsq
  have hfin : (2 : ℕ) ^ n ≡ 2 ^ k [MOD 2 ^ (k + 1)] := by
    have h1 : (2 : ℕ) ^ n + 1 ≡ 2 ^ k + 1 [MOD 2 ^ (k + 1)] := by
      calc (2 : ℕ) ^ n + 1 = u ^ m := heq.symm
        _ ≡ u [MOD 2 ^ (k + 1)] := hpow
        _ = 2 ^ k + 1 := hk'
    exact Nat.ModEq.add_right_cancel' 1 h1
  have hn : k + 1 ≤ n := by
    have h3 : u ^ 3 ≤ u ^ m := Nat.pow_le_pow_right (by omega) hm
    have h4 : (2 : ℕ) ^ (k + 1) < 2 ^ n := by
      have hu3 : u ^ 3 = u * u * u := by ring
      nlinarith [heq, hu2, hkk]
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).1 h4
    omega
  exact not_modEq_pow_two hn hfin

/-! ### The solved cases -/

/-- There is no solution of Catalan's equation with `x = 2`: the equation `2 ^ p - y ^ q = 1`
has no solutions with `p, q, y ≥ 2`. -/
theorem no_catalan_solution_base_two (p y q : ℕ) : ¬ IsCatalanSolution 2 p y q := by
  rintro ⟨-, hp, hy, hq, heq⟩
  -- `y` is odd, hence `y ≥ 3`
  have h2p : (2 : ℕ) ∣ 2 ^ p := dvd_pow_self 2 (by omega)
  have hyodd : ¬ (2 ∣ y) := by
    intro hdvd
    have : (2 : ℕ) ∣ y ^ q := dvd_pow hdvd (by omega)
    omega
  have hy3 : 3 ≤ y := by omega
  rcases Nat.even_or_odd q with hqe | hqo
  · -- even exponent: `2 ^ p = z ^ 2 + 1` with `z` odd, impossible mod `4`
    obtain ⟨t, ht⟩ := hqe
    have ht1 : 1 ≤ t := by omega
    have hz : y ^ q = (y ^ t) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    set z := y ^ t with hzdef
    have hzodd : ¬ (2 ∣ z) := by
      intro hdvd
      exact hyodd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd)
    obtain ⟨s, hs⟩ : ∃ s, z = 2 * s + 1 := ⟨z / 2, by omega⟩
    have h4 : (4 : ℕ) ∣ 2 ^ p := by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ p := pow_dvd_pow 2 (by omega)
      simpa using this
    have hzz : z ^ 2 = 4 * (s * s + s) + 1 := by rw [hs]; ring
    rw [hz, hzz] at heq
    omega
  · -- odd exponent
    have hq3 : 3 ≤ q := by
      rcases hqo with ⟨t, ht⟩; omega
    exact odd_pow_add_one_ne_two_pow hy3 hq3 hqo heq.symm

/-- The only solution of Catalan's equation with `y = 2` is `3 ^ 2 = 2 ^ 3 + 1`. -/
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
theorem catalan_coprime_exponents {x p y q : ℕ} (h : IsCatalanSolution x p y q) :
    Nat.Coprime p q := by
  obtain ⟨hx, hp, hy, hq, heq⟩ := h
  by_contra hc
  set d := Nat.gcd p q with hd
  have hdp : d ∣ p := Nat.gcd_dvd_left p q
  have hdq : d ∣ q := Nat.gcd_dvd_right p q
  have hd0 : d ≠ 0 := by
    intro h0
    have : p = 0 := Nat.eq_zero_of_gcd_eq_zero_left h0
    omega
  have hd2 : 2 ≤ d := by
    rcases Nat.lt_or_ge d 2 with h | h
    · have hd1 : d = 1 := by omega
      exact absurd (show Nat.Coprime p q by rw [Nat.Coprime, ← hd]; exact hd1) hc
    · exact h
  have hxp : x ^ p = (x ^ (p / d)) ^ d := by
    rw [← pow_mul, Nat.div_mul_cancel hdp]
  have hyq : y ^ q = (y ^ (q / d)) ^ d := by
    rw [← pow_mul, Nat.div_mul_cancel hdq]
  rw [hxp, hyq] at heq
  exact pow_ne_pow_add_one (Nat.one_le_pow _ _ (by omega)) hd2 heq

/-- Reduction to prime exponents: from any solution one obtains a solution with prime
exponents and bases at least as large. -/
theorem catalan_reduce_to_prime_exponents {x p y q : ℕ} (h : IsCatalanSolution x p y q) :
    ∃ X P Y Q : ℕ, IsCatalanSolution X P Y Q ∧ P.Prime ∧ Q.Prime ∧ x ≤ X ∧ y ≤ Y := by
  obtain ⟨hx, hp, hy, hq, heq⟩ := h
  have hpp : (Nat.minFac p).Prime := Nat.minFac_prime (by omega)
  have hqp : (Nat.minFac q).Prime := Nat.minFac_prime (by omega)
  have hdp : Nat.minFac p ∣ p := Nat.minFac_dvd p
  have hdq : Nat.minFac q ∣ q := Nat.minFac_dvd q
  have hp1 : 1 ≤ p / Nat.minFac p := Nat.one_le_div_iff (hpp.pos) |>.2 (Nat.minFac_le (by omega))
  have hq1 : 1 ≤ q / Nat.minFac q := Nat.one_le_div_iff (hqp.pos) |>.2 (Nat.minFac_le (by omega))
  refine ⟨x ^ (p / Nat.minFac p), Nat.minFac p, y ^ (q / Nat.minFac q), Nat.minFac q,
    ⟨?_, hpp.two_le, ?_, hqp.two_le, ?_⟩, hpp, hqp, ?_, ?_⟩
  · calc 2 ≤ x := hx
      _ = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (p / Nat.minFac p) := Nat.pow_le_pow_right (by omega) hp1
  · calc 2 ≤ y := hy
      _ = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ (q / Nat.minFac q) := Nat.pow_le_pow_right (by omega) hq1
  · rw [← pow_mul, ← pow_mul, Nat.div_mul_cancel hdp, Nat.div_mul_cancel hdq]
    exact heq
  · calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (p / Nat.minFac p) := Nat.pow_le_pow_right (by omega) hp1
  · calc y = y ^ 1 := (pow_one y).symm
      _ ≤ y ^ (q / Nat.minFac q) := Nat.pow_le_pow_right (by omega) hq1

/-- A Lean-checked reduction of the Catalan–Mihăilescu theorem: it suffices to rule out
solutions with prime exponents and both bases at least `3`. -/
theorem catalan_mihailescu_reduction
    (H : ∀ X P Y Q : ℕ, P.Prime → Q.Prime → 3 ≤ X → 3 ≤ Y → X ^ P ≠ Y ^ Q + 1) :
    CatalanMihailescuStatement := by
  intro x p y q hsol
  rcases Nat.lt_or_ge x 3 with hx3 | hx3
  · -- `x = 2` is impossible
    exfalso
    have hx2 : x = 2 := by have := hsol.1; omega
    subst hx2
    exact no_catalan_solution_base_two p y q hsol
  rcases Nat.lt_or_ge y 3 with hy3 | hy3
  · -- `y = 2` gives exactly the known solution
    have hy2 : y = 2 := by have := hsol.2.2.1; omega
    subst hy2
    obtain ⟨hx, hp, hq⟩ := catalan_solution_of_rhs_base_two hsol
    subst hx; subst hp; subst hq
    rfl
  · exfalso
    obtain ⟨X, P, Y, Q, hsol', hP, hQ, hxX, hyY⟩ := catalan_reduce_to_prime_exponents hsol
    exact H X P Y Q hP hQ (by omega) (by omega) hsol'.2.2.2.2

/-! ### An exhaustive check in a finite range -/

instance decidableIsCatalanSolution (x p y q : ℕ) : Decidable (IsCatalanSolution x p y q) := by
  unfold IsCatalanSolution
  infer_instance

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- Exhaustive verification: in the range `x, y < 50` and `p, q < 8` the only pair of
consecutive perfect powers is `9 = 3 ^ 2` and `8 = 2 ^ 3`. -/
theorem catalan_check_small : ∀ x < 50, ∀ p < 8, ∀ y < 50, ∀ q < 8,
    IsCatalanSolution x p y q → (x, p, y, q) = (3, 2, 2, 3) := by decide

/-! ### The target -/

/-- **Catalan–Mihăilescu: base cases and a Lean-checked reduction.**

* `9 = 3 ^ 2` and `8 = 2 ^ 3` are consecutive perfect powers;
* every solution of `x ^ p = y ^ q + 1` (with `x, y, p, q ≥ 2`) in which one of the bases
  equals `2`, or in which the exponents have a common factor, is exactly `3 ^ 2 = 2 ^ 3 + 1`;
* in the finite range `x, y < 50`, `p, q < 8` an exhaustive check confirms there is no other
  solution;
* the general statement follows once one rules out solutions with prime exponents and both
  bases at least `3`. -/
theorem Catalan_Mihailescu :
    IsCatalanSolution 3 2 2 3 ∧
    (∀ x p y q : ℕ, IsCatalanSolution x p y q →
        (x = 2 ∨ y = 2 ∨ ¬ Nat.Coprime p q) → (x, p, y, q) = (3, 2, 2, 3)) ∧
    (∀ x < 50, ∀ p < 8, ∀ y < 50, ∀ q < 8,
        IsCatalanSolution x p y q → (x, p, y, q) = (3, 2, 2, 3)) ∧
    ((∀ X P Y Q : ℕ, P.Prime → Q.Prime → 3 ≤ X → 3 ≤ Y → X ^ P ≠ Y ^ Q + 1) →
      CatalanMihailescuStatement) := by
  refine ⟨isCatalanSolution_nine_eight, ?_, catalan_check_small, catalan_mihailescu_reduction⟩
  rintro x p y q hsol (rfl | rfl | hcop)
  · exact absurd hsol (no_catalan_solution_base_two p y q)
  · obtain ⟨hx, hp, hq⟩ := catalan_solution_of_rhs_base_two hsol
    subst hx; subst hp; subst hq
    rfl
  · exact absurd (catalan_coprime_exponents hsol) hcop

end Frontier

