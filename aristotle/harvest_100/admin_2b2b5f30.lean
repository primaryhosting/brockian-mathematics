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
def CatalanMihailescuStatement : Prop :=
  ∀ x y p q : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → x ^ p - y ^ q = 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-! ### Elementary auxiliary estimates and identities -/

/-- A crude but sufficient strict growth estimate: `(b+1) ^ n` exceeds `b ^ n` by at least
`2 * b + 1` as soon as `n ≥ 2`. -/
lemma succ_pow_ge (b n : ℕ) (hb : 1 ≤ b) (hn : 2 ≤ n) :
    b ^ n + 2 * b + 1 ≤ (b + 1) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => ring_nf; nlinarith
  | succ n hn ih =>
      have h1 : (b + 1) ^ (n + 1) = (b + 1) ^ n * (b + 1) := by ring
      have h2 : b ^ (n + 1) = b ^ n * b := by ring
      nlinarith [pow_pos (show 0 < b by omega) n]

/-- The geometric sum identity over `ℕ`, in the form `(∑ i < p, x ^ i) * (x - 1) + 1 = x ^ p`
with `x = c + 1`. -/
lemma geom_nat (c p : ℕ) : (∑ i ∈ Finset.range p, (c + 1) ^ i) * c + 1 = (c + 1) ^ p := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ]; ring_nf; ring_nf at ih; nlinarith [ih]

/-- The "alternating" geometric sum identity over `ℕ`: for odd exponents `2 * m + 1`,
`y + 1` divides `y ^ (2 * m + 1) + 1`, with an explicit cofactor which is visibly odd
when `y = w + 1` and `w` is even. -/
lemma geom_alt_nat (w m : ℕ) :
    ((∑ k ∈ Finset.range m, (w + 1) ^ (2 * k + 1) * w) + 1) * (w + 2)
      = (w + 1) ^ (2 * m + 1) + 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      ring_nf
      ring_nf at ih
      nlinarith [ih]

/-- Binomial expansion modulo `d ^ 2`: `(1 + d) ^ i = 1 + i * d + M * d ^ 2`. -/
lemma pow_one_add_expand (d i : ℕ) : ∃ M, (1 + d) ^ i = 1 + i * d + M * (d * d) := by
  induction i with
  | zero => exact ⟨0, by ring⟩
  | succ i ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨i + M + M * d, ?_⟩
      rw [pow_succ, hM]
      ring

/-- Geometric sum modulo `d ^ 2`: `2 * ∑ i < m, (1 + d) ^ i = 2 * m + m * (m - 1) * d + K * d ^ 2`. -/
lemma geom_sum_expand (d m : ℕ) :
    ∃ K, 2 * (∑ i ∈ Finset.range m, (1 + d) ^ i) = 2 * m + m * (m - 1) * d + K * (d * d) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨M, hM⟩ := pow_one_add_expand d m
      refine ⟨K + 2 * M, ?_⟩
      rw [Finset.sum_range_succ, Nat.mul_add, hK, hM]
      cases m with
      | zero => simp; ring
      | succ m => simp; ring

/-- Binomial expansion modulo `D ^ 2` over `ℤ`. -/
lemma pow_one_add_expand_int (D : ℤ) (i : ℕ) :
    ∃ M : ℤ, (1 + D) ^ i = 1 + i * D + M * (D * D) := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨i + M + M * D, ?_⟩
      rw [pow_succ, hM]
      push_cast
      ring

/-- Geometric sum modulo `D ^ 2` over `ℤ`. -/
lemma geom_sum_expand_int (D : ℤ) (m : ℕ) :
    ∃ K : ℤ, 2 * (∑ i ∈ Finset.range m, (1 + D) ^ i)
      = 2 * m + m * ((m : ℤ) - 1) * D + K * (D * D) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨M, hM⟩ := pow_one_add_expand_int D m
      refine ⟨K + 2 * M, ?_⟩
      rw [Finset.sum_range_succ, mul_add, hK, hM]
      push_cast
      ring

/-- For odd `q`, `Y + 1` divides `Y ^ q + 1` with the alternating geometric sum as cofactor. -/
lemma neg_geom_mul (Y : ℤ) {q : ℕ} (hq : Odd q) :
    (∑ i ∈ Finset.range q, (-Y) ^ i) * (Y + 1) = Y ^ q + 1 := by
  have h := geom_sum_mul (-Y) q
  rw [hq.neg_pow] at h
  linarith [h]

/-- A positive integer divisor of `r ^ m` (`r` prime) is a power of `r`. -/
lemma int_dvd_prime_pow {A : ℤ} (hA : 0 < A) {r m : ℕ} (hr : r.Prime) (h : A ∣ (r:ℤ) ^ m) :
    ∃ u, u ≤ m ∧ A = (r:ℤ) ^ u := by
  have h1 : A.natAbs ∣ r ^ m := by
    have h2 := Int.natAbs_dvd_natAbs.mpr h
    simpa [Int.natAbs_pow] using h2
  obtain ⟨u, hu, h'⟩ := (Nat.dvd_prime_pow hr).1 h1
  refine ⟨u, hu, ?_⟩
  have habs : (A.natAbs : ℤ) = A := Int.natAbs_of_nonneg hA.le
  rw [← habs, h']
  push_cast
  ring

lemma lt_two_pow_sub {r : ℕ} (h : 5 ≤ r) : r < 2 ^ (r - 2) := by
  induction r, h using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have h1 : 2 ^ (r + 1 - 2) = 2 * 2 ^ (r - 2) := by
        rw [show r + 1 - 2 = (r - 2) + 1 by omega, pow_succ]; ring
      omega

/-! ### Special cases of Catalan's equation -/

/-- Two perfect powers with the *same* exponent are never consecutive. -/
lemma catalan_equal_exponents {x y n : ℕ} (hy : 1 ≤ y) (hn : 2 ≤ n) :
    x ^ n ≠ y ^ n + 1 := by
  intro h
  have hxy : y < x := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_left hc n
    omega
  have h1 : (y + 1) ^ n ≤ x ^ n := Nat.pow_le_pow_left hxy n
  have h2 := succ_pow_ge y n hy hn
  omega

/-- Two perfect powers with *both* exponents even are never consecutive. -/
lemma catalan_even_even {x y p q : ℕ} (hy : 1 ≤ y) (hp : Even p) (hq : Even q) :
    x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨m, rfl⟩ := hp
  obtain ⟨k, rfl⟩ := hq
  have h1 : (x ^ m) ^ 2 = (y ^ k) ^ 2 + 1 := by
    rw [← pow_mul, ← pow_mul]; ring_nf; ring_nf at h; omega
  exact catalan_equal_exponents (Nat.one_le_iff_ne_zero.2 (by positivity)) le_rfl h1

/-- `x ^ 2 = y ^ q + 1` has no solutions with `y` odd, `y > 1` and `q ≥ 2`. -/
lemma catalan_sq_odd {x y q : ℕ} (hy : 1 < y) (hq : 2 ≤ q) (hodd : Odd y) :
    x ^ 2 ≠ y ^ q + 1 := by
  intro h
  have hyq : Odd (y ^ q) := hodd.pow
  have hx2 : Even (x ^ 2) := by
    rcases hyq with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hxe : Even x := by
    rcases Nat.even_or_odd x with he | ho
    · exact he
    · exact absurd hx2 (by simpa using (ho.pow (n := 2)))
  have hy3 : 3 ≤ y := by
    rcases hodd with ⟨k, hk⟩; omega
  have hyq3 : 9 ≤ y ^ q := by
    calc (9:ℕ) = 3 ^ 2 := by norm_num
    _ ≤ y ^ q := Nat.pow_le_pow_left hy3 2 |>.trans (Nat.pow_le_pow_right (by omega) hq)
  have hx4 : 4 ≤ x := by nlinarith [h, hyq3]
  obtain ⟨c, rfl⟩ : ∃ c, x = c + 1 := ⟨x - 1, by omega⟩
  have hfac : c * (c + 2) = y ^ q := by ring_nf; ring_nf at h; omega
  have hcop : Nat.Coprime c (c + 2) := by
    have hd : Nat.gcd c (c + 2) ∣ 2 := by
      have h1 : Nat.gcd c (c + 2) ∣ (c + 2) - c :=
        Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
      simpa using h1
    have hoddc : Odd c := by rcases hxe with ⟨m, hm⟩; exact ⟨m - 1, by omega⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h1
    · exact h1
    · exfalso
      have : (2:ℕ) ∣ c := h1 ▸ Nat.gcd_dvd_left c (c + 2)
      rcases hoddc with ⟨m, hm⟩; omega
  obtain ⟨b, hb⟩ : ∃ b, c = b ^ q :=
    exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) hfac
  obtain ⟨a, ha⟩ : ∃ a, c + 2 = a ^ q :=
    exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm) (by rw [mul_comm]; exact hfac)
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hbp
    · rw [zero_pow (by omega)] at hb; omega
    · omega
  have hab : b < a := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_left hc q
    omega
  have h1 : (b + 1) ^ q ≤ a ^ q := Nat.pow_le_pow_left hab q
  have h2 := succ_pow_ge b q hb1 hq
  omega

/-- `x ^ p = y ^ q + 1` has no solutions with `p` even and `y` odd. -/
lemma catalan_p_even_odd_y {x y p q : ℕ} (hy : 1 < y) (hq : 2 ≤ q) (hp : Even p)
    (hodd : Odd y) : x ^ p ≠ y ^ q + 1 := by
  intro h
  obtain ⟨m, rfl⟩ := hp
  refine catalan_sq_odd hy hq hodd (x := x ^ m) ?_
  rw [← pow_mul, show m * 2 = m + m by ring]
  exact h

/-- Catalan's equation when the smaller power is a power of two:
`x ^ p = 2 ^ q + 1` forces `9 = 8 + 1`. -/
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
lemma catalan_two_pow_sub_one {y p q : ℕ} (hy : 1 < y) (hp : 1 < p) (hq : 1 < q) :
    2 ^ p ≠ y ^ q + 1 := by
  intro h
  have h4 : (4:ℕ) ∣ 2 ^ p := by
    have : (2:ℕ) ^ 2 ∣ 2 ^ p := pow_dvd_pow 2 (by omega)
    simpa using this
  have hyodd : Odd y := by
    rcases Nat.even_or_odd y with he | ho
    · exfalso
      have : Even (y ^ q) := (Nat.even_pow (n := q)).2 ⟨he, by omega⟩
      rcases this with ⟨t, ht⟩
      rcases h4 with ⟨s, hs⟩
      omega
    · exact ho
  obtain ⟨w, hyw, hwe⟩ : ∃ w, y = w + 1 ∧ Even w := by
    rcases hyodd with ⟨t, ht⟩
    exact ⟨2 * t, by omega, ⟨t, by ring⟩⟩
  subst hyw
  rcases Nat.even_or_odd q with hqe | hqo
  · -- even exponent: `2 ^ p ≡ 2 (mod 4)`, impossible
    obtain ⟨k, rfl⟩ := hqe
    have hZ : Odd ((w + 1) ^ k) := hyodd.pow
    rcases hZ with ⟨t, ht⟩
    have hsplit : (w + 1) ^ (k + k) = ((w + 1) ^ k) * ((w + 1) ^ k) := by rw [← pow_add]
    rcases h4 with ⟨s, hs⟩
    rw [hsplit, ht] at h
    have : (2 * t + 1) * (2 * t + 1) + 1 = 4 * (t * t + t) + 2 := by ring
    omega
  · -- odd exponent: `y + 1` carries the full power of two
    obtain ⟨m, rfl⟩ := hqo
    have hm : 1 ≤ m := by omega
    have hkey := geom_alt_nat w m
    set C := (∑ k ∈ Finset.range m, (w + 1) ^ (2 * k + 1) * w) + 1 with hC
    have hCodd : Odd C := by
      have hev : Even (∑ k ∈ Finset.range m, (w + 1) ^ (2 * k + 1) * w) := by
        apply Finset.even_sum
        intro i _
        exact hwe.mul_left _
      rcases hev with ⟨t, ht⟩
      exact ⟨t, by omega⟩
    have hCdvd : C ∣ 2 ^ p := ⟨w + 2, by omega⟩
    obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hCdvd
    have hC1 : C = 1 := by
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · simpa using hCi
      · exfalso
        rw [hCi] at hCodd
        rcases hCodd with ⟨t, ht⟩
        have h2 : (2:ℕ) ∣ 2 ^ i := dvd_pow_self 2 hipos.ne'
        omega
    rw [hC1, one_mul] at hkey
    have hge : (w + 1) ^ 2 ≤ (w + 1) ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hw1 : 1 ≤ w := by omega
    nlinarith [hge, hkey]

/-- **Catalan's equation with a prime power on the smaller side.**
`x ^ p = r ^ n + 1` with `r` prime, `x, p, n > 1` forces `9 = 8 + 1`. -/
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
lemma catalan_prime_power_base {x y p q r k : ℕ} (hr : r.Prime) (hyk : y = r ^ k)
    (hx : 1 < x) (hy : 1 < y) (hp : 1 < p) (hq : 1 < q) (h : x ^ p = y ^ q + 1) :
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by
  subst hyk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h'
    · simp at hy
    · exact h'
  have h' : x ^ p = r ^ (k * q) + 1 := by rw [pow_mul]; exact h
  have hn : 1 < k * q := by nlinarith
  obtain ⟨h1, h2, h3, h4⟩ := catalan_prime_base hr hx hp hn h'
  subst h3
  have hk3 : k ≤ 3 := Nat.le_of_dvd (by omega) ⟨q, h4.symm⟩
  have hkq : k = 1 ∧ q = 3 := by
    interval_cases k <;> omega
  obtain ⟨hk, hq3⟩ := hkq
  subst hk
  exact ⟨h1, h2, by norm_num, hq3⟩

/-! ### The larger base a prime power -/

/-- The auxiliary equation `z ^ r + 1 = r * (z + 1)` only has the solution `2 ^ 3 + 1 = 3 * 3`. -/
lemma catalan_small_eq {z r : ℕ} (hz : 2 ≤ z) (hr : 3 ≤ r) (h : z ^ r + 1 = r * (z + 1)) :
    r = 3 ∧ z = 2 := by
  have hr5 : r < 5 := by
    by_contra hc
    push_neg at hc
    have h1 : z * 2 ^ (r - 1) ≤ z ^ r := by
      have hpow : 2 ^ (r - 1) ≤ z ^ (r - 1) := Nat.pow_le_pow_left hz _
      calc z * 2 ^ (r - 1) ≤ z * z ^ (r - 1) := Nat.mul_le_mul_left _ hpow
      _ = z ^ r := by rw [← pow_succ']; congr 1; omega
    have h2 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
      rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]; ring
    have h3 : r < 2 ^ (r - 2) := lt_two_pow_sub hc
    nlinarith [h1, h2, h3, h]
  have hr34 : r = 3 ∨ r = 4 := by omega
  have hz2 : z = 2 := by
    by_contra hc
    have hz3 : 3 ≤ z := by omega
    have h9 : 9 * z ≤ z ^ 3 := by
      have hcube : z ^ 3 = z * z * z := by ring
      nlinarith [hz3]
    have h34 : z ^ 3 ≤ z ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    rcases hr34 with rfl | rfl <;> omega
  subst hz2
  rcases hr34 with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exfalso; norm_num at h

/-- First stage for the larger base: if `r ^ m = y ^ q + 1` with `r` an odd prime and `q` odd,
then `r` divides `q`. -/
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
lemma catalan_prime_pow_larger {y q r m : ℕ} (hr : r.Prime) (hy : 1 < y) (hq : 1 < q)
    (hqodd : Odd q) (hm : 1 < m) (h : r ^ m = y ^ q + 1) : r = 3 ∧ m = 2 ∧ y = 2 ∧ q = 3 := by
  rcases eq_or_ne r 2 with rfl | hr2
  · exact absurd h (catalan_two_pow_sub_one hy hm hq)
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨q', rfl⟩ := catalan_stage_one hr hr3 hy hq hqodd h
  have hq'1 : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with rfl | h'
    · simp at hq
    · exact h'
  have hz : 2 ≤ y ^ q' := by
    calc 2 ≤ y := hy
    _ = y ^ 1 := (pow_one y).symm
    _ ≤ y ^ q' := Nat.pow_le_pow_right (by omega) hq'1
  have hstage : r ^ m = (y ^ q') ^ r + 1 := by rw [← pow_mul, mul_comm q' r]; exact h
  obtain ⟨h1, h2, h3⟩ := catalan_stage_two hr hrodd hr3 hz hstage
  have hy2 : y = 2 ∧ q' = 1 := by
    rcases Nat.lt_or_ge q' 2 with hlt | hge
    · have hq'eq : q' = 1 := by omega
      subst hq'eq
      simpa using h2
    · exfalso
      have hpow : y ^ 2 ≤ y ^ q' := Nat.pow_le_pow_right (by omega) hge
      nlinarith [h2, hpow]
  obtain ⟨hy2', hq'2⟩ := hy2
  subst hq'2
  exact ⟨h1, h3, hy2', by omega⟩

/-- **Catalan's equation when the larger base is a prime power and `q` is odd.**
The only solution is `3 ^ 2 - 2 ^ 3 = 1`. -/
lemma catalan_prime_power_larger {x y p q r k : ℕ} (hr : r.Prime) (hxk : x = r ^ k) (hx : 1 < x)
    (hy : 1 < y) (hp : 1 < p) (hq : 1 < q) (hqodd : Odd q) (h : x ^ p = y ^ q + 1) :
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by
  subst hxk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h'
    · simp at hx
    · exact h'
  have hm : 1 < k * p := by nlinarith
  have h' : r ^ (k * p) = y ^ q + 1 := by rw [pow_mul]; exact h
  obtain ⟨h1, h2, h3, h4⟩ := catalan_prime_pow_larger hr hy hq hqodd hm h'
  subst h1
  have hk : k = 1 ∧ p = 2 := by
    have hk2 : k ≤ 2 := Nat.le_of_dvd (by omega) ⟨p, h2.symm⟩
    interval_cases k <;> omega
  obtain ⟨hk1', hp2⟩ := hk
  subst hk1'
  exact ⟨by norm_num, hp2, h3, h4⟩

/-- If the larger base is a power of two there is no solution at all. -/
lemma catalan_two_power_larger {y p q k : ℕ} (hy : 1 < y) (hp : 1 < p) (hq : 1 < q) (hk : 1 ≤ k) :
    (2 ^ k) ^ p ≠ y ^ q + 1 := by
  rw [← pow_mul]
  exact catalan_two_pow_sub_one hy (by nlinarith) hq

/-- A reduction: any solution with `q` even has `x` odd, `y` even and `p` odd. -/
lemma catalan_q_even_reduction {x y p q : ℕ} (hy : 1 < y) (hp : 1 < p) (hq : 1 < q)
    (h : x ^ p = y ^ q + 1) (hqe : Even q) : Odd x ∧ Even y ∧ Odd p := by
  obtain ⟨k, rfl⟩ := hqe
  have hk : k ≠ 0 := by omega
  have hsplit : y ^ (k + k) = (y ^ k) * (y ^ k) := by rw [← pow_add]
  have hZeven : Even (y ^ k) := by
    rcases Nat.even_or_odd (y ^ k) with he | ho
    · exact he
    · exfalso
      rcases ho with ⟨t, ht⟩
      have hxe : Even x := by
        rcases Nat.even_or_odd x with he' | ho'
        · exact he'
        · exfalso
          have : Odd (x ^ p) := ho'.pow
          rcases this with ⟨s, hs⟩
          rw [hsplit, ht] at h
          have hexp : (2 * t + 1) * (2 * t + 1) + 1 = 2 * (2 * t * t + 2 * t + 1) := by ring
          omega
      have h4 : (4:ℕ) ∣ x ^ p := by
        obtain ⟨u, hu⟩ := hxe
        have : (2:ℕ) ^ 2 ∣ x ^ p := by
          have h2 : (2:ℕ) ∣ x := ⟨u, by omega⟩
          calc (2:ℕ) ^ 2 ∣ x ^ 2 := pow_dvd_pow_of_dvd h2 2
          _ ∣ x ^ p := pow_dvd_pow x (by omega)
        simpa using this
      rw [hsplit, ht] at h
      rcases h4 with ⟨s, hs⟩
      have hexp : (2 * t + 1) * (2 * t + 1) + 1 = 4 * (t * t + t) + 2 := by ring
      omega
  have hyeven : Even y := by
    rcases Nat.even_or_odd y with he | ho
    · exact he
    · exact absurd hZeven (by simpa using ho.pow (n := k))
  have hxodd : Odd x := by
    rcases Nat.even_or_odd x with he | ho
    · exfalso
      have hxp : Even (x ^ p) := (Nat.even_pow (n := p)).2 ⟨he, by omega⟩
      have hyq : Even (y ^ (k + k)) := by
        rw [hsplit]
        exact hZeven.mul_right _
      rcases hxp with ⟨s, hs⟩; rcases hyq with ⟨t, ht⟩; omega
    · exact ho
  refine ⟨hxodd, hyeven, ?_⟩
  rcases Nat.even_or_odd p with he | ho
  · exact absurd h (catalan_even_even (by omega) he ⟨k, rfl⟩)
  · exact ho

/-! ### A finite verification -/

set_option maxRecDepth 1000000 in
/-- Exhaustive kernel check of Catalan's equation in the box `x, y ≤ 100`, `p, q ≤ 13`,
for powers of size at most `10000`. -/
theorem catalan_check :
    ∀ x ∈ Finset.range 101, ∀ p ∈ Finset.range 14, 1 < x → 1 < p → x ^ p ≤ 10000 →
      ∀ y ∈ Finset.range 101, ∀ q ∈ Finset.range 14, 1 < y → 1 < q → x ^ p = y ^ q + 1 →
        x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by decide +kernel

/-- Catalan–Mihăilescu, verified for all perfect powers up to `10000`. -/
lemma catalan_bounded {x y p q : ℕ} (hx : 1 < x) (hy : 1 < y) (hp : 1 < p) (hq : 1 < q)
    (hbound : x ^ p ≤ 10000) (h : x ^ p = y ^ q + 1) : x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3 := by
  have hxb : x < 101 := by
    by_contra hc
    push_neg at hc
    have h1 : x ^ 2 ≤ x ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (101:ℕ) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hc 2
    norm_num at h2
    omega
  have hpb : p < 14 := by
    by_contra hc
    push_neg at hc
    have h1 : (2:ℕ) ^ p ≤ x ^ p := Nat.pow_le_pow_left (by omega) p
    have h2 : (2:ℕ) ^ 14 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hc
    norm_num at h2
    omega
  have hyq : y ^ q ≤ 10000 := by omega
  have hyb : y < 101 := by
    by_contra hc
    push_neg at hc
    have h1 : y ^ 2 ≤ y ^ q := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (101:ℕ) ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hc 2
    norm_num at h2
    omega
  have hqb : q < 14 := by
    by_contra hc
    push_neg at hc
    have h1 : (2:ℕ) ^ q ≤ y ^ q := Nat.pow_le_pow_left (by omega) q
    have h2 : (2:ℕ) ^ 14 ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hc
    norm_num at h2
    omega
  exact catalan_check x (Finset.mem_range.2 hxb) p (Finset.mem_range.2 hpb) hx hp hbound
    y (Finset.mem_range.2 hyb) q (Finset.mem_range.2 hqb) hy hq h

/-- If `z ^ n = v < 4` with `z > 1` and `n ≥ 1`, then `n = 1` and `z = v`. -/
lemma pow_eq_of_lt_four {z n v : ℕ} (hz : 1 < z) (hn : 1 ≤ n) (hv : v < 4) (h : z ^ n = v) :
    n = 1 ∧ z = v := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    exact ⟨rfl, by simpa using h⟩
  · exfalso
    have h1 : 2 ^ n ≤ z ^ n := Nat.pow_le_pow_left hz n
    have h3 : (2:ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    norm_num at h3
    omega

/-- **Reduction to prime exponents.**  If Catalan's equation has no nontrivial solutions with
both exponents prime (other than `3 ^ 2 - 2 ^ 3 = 1`), then it has none at all: the full
statement `CatalanMihailescuStatement` follows. -/
lemma catalan_prime_exponents_reduction
    (H : ∀ x y p q : ℕ, 1 < x → 1 < y → p.Prime → q.Prime → x ^ p = y ^ q + 1 →
      x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) : CatalanMihailescuStatement := by
  intro x y p q hx hy hp hq h
  have h' : x ^ p = y ^ q + 1 := by omega
  have hlp : (p.minFac).Prime := Nat.minFac_prime (by omega)
  have hmp : (q.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨p', hp'⟩ : p.minFac ∣ p := Nat.minFac_dvd p
  obtain ⟨q', hq'⟩ : q.minFac ∣ q := Nat.minFac_dvd q
  have hp'pos : 1 ≤ p' := by
    rcases Nat.eq_zero_or_pos p' with rfl | h''
    · simp at hp'; omega
    · exact h''
  have hq'pos : 1 ≤ q' := by
    rcases Nat.eq_zero_or_pos q' with rfl | h''
    · simp at hq'; omega
    · exact h''
  have hX : 1 < x ^ p' := Nat.one_lt_pow (by omega) hx
  have hY : 1 < y ^ q' := Nat.one_lt_pow (by omega) hy
  have hkey : (x ^ p') ^ p.minFac = (y ^ q') ^ q.minFac + 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm p' p.minFac, mul_comm q' q.minFac, ← hp', ← hq']
    exact h'
  obtain ⟨h1, h2, h3, h4⟩ := H _ _ _ _ hX hY hlp hmp hkey
  obtain ⟨hp1, hx3⟩ := pow_eq_of_lt_four hx hp'pos (by norm_num) h1
  obtain ⟨hq1, hy2⟩ := pow_eq_of_lt_four hy hq'pos (by norm_num) h3
  refine ⟨hx3, ?_, hy2, ?_⟩
  · rw [hp', hp1, h2]
  · rw [hq', hq1, h4]

/-! ### Main theorem -/

/-- **Catalan–Mihăilescu: base case and Lean-checked reductions.**

The full statement is recorded as `Frontier.CatalanMihailescuStatement`.  What is proved here:

* the full conjecture reduces to the case of prime exponents
  (`catalan_prime_exponents_reduction`);

* `8` and `9` really are consecutive perfect powers (`3 ^ 2 - 2 ^ 3 = 1`);
* the theorem holds in full whenever the larger base is a power of `2`, or the smaller base is a
  prime power: the only solution is then `3 ^ 2 - 2 ^ 3 = 1`;
* the theorem holds in full whenever the larger base is a prime power and `q` is odd;
* no two perfect powers with the same exponent are consecutive;
* no two perfect powers with both exponents even are consecutive;
* there is no solution with `p` even and `y` odd;
* every solution with `q` even has `x` odd, `y` even and `p` odd;
* the theorem holds for all perfect powers up to `10000` (exhaustive kernel check). -/
theorem Catalan_Mihailescu :
    (3 ^ 2 - 2 ^ 3 = 1) ∧
    (∀ x y p q : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → x ^ p - y ^ q = 1 →
        ((∃ k : ℕ, 1 ≤ k ∧ x = 2 ^ k) ∨ ∃ r k : ℕ, r.Prime ∧ y = r ^ k) →
        x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) ∧
    (∀ x y p q r k : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → Odd q → r.Prime → x = r ^ k →
        x ^ p - y ^ q = 1 → x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) ∧
    (∀ x y p q : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → x ^ p ≤ 10000 → x ^ p - y ^ q = 1 →
        x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) ∧
    (∀ x y n : ℕ, 1 < y → 1 < n → x ^ n - y ^ n ≠ 1) ∧
    (∀ x y p q : ℕ, 1 < y → Even p → Even q → x ^ p - y ^ q ≠ 1) ∧
    (∀ x y p q : ℕ, 1 < y → 1 < q → Even p → Odd y → x ^ p - y ^ q ≠ 1) ∧
    (∀ x y p q : ℕ, 1 < y → 1 < p → 1 < q → x ^ p - y ^ q = 1 → Even q →
        Odd x ∧ Even y ∧ Odd p) ∧
    ((∀ x y p q : ℕ, 1 < x → 1 < y → p.Prime → q.Prime → x ^ p = y ^ q + 1 →
        x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) → CatalanMihailescuStatement) := by
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, catalan_prime_exponents_reduction⟩
  · rintro x y p q hx hy hp hq h (⟨k, hk, rfl⟩ | ⟨r, k, hr, rfl⟩)
    · exact absurd (by omega : ((2:ℕ) ^ k) ^ p = y ^ q + 1)
        (catalan_two_power_larger hy hp hq hk)
    · exact catalan_prime_power_base hr rfl hx hy hp hq (by omega)
  · intro x y p q r k hx hy hp hq hqodd hr hxk h
    exact catalan_prime_power_larger hr hxk hx hy hp hq hqodd (by omega)
  · intro x y p q hx hy hp hq hbound h
    exact catalan_bounded hx hy hp hq hbound (by omega)
  · intro x y n hy hn h
    have h' : x ^ n = y ^ n + 1 := by omega
    exact catalan_equal_exponents (by omega) hn h'
  · intro x y p q hy hp hq h
    have h' : x ^ p = y ^ q + 1 := by omega
    exact catalan_even_even (by omega) hp hq h'
  · intro x y p q hy hq hp hodd h
    have h' : x ^ p = y ^ q + 1 := by omega
    exact catalan_p_even_odd_y hy hq hp hodd h'
  · intro x y p q hy hp hq h hqe
    have h' : x ^ p = y ^ q + 1 := by omega
    exact catalan_q_even_reduction hy hp hq h' hqe

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

