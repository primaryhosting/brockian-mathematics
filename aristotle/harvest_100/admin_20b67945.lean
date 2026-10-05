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
def CatalanMihailescuStatement : Prop :=
  ∀ x y p q : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → x ^ p = y ^ q + 1 →
    x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3

/-! ## A Lean-checked reduction: it suffices to treat prime exponents -/

private lemma pow_eq_small {x n c : ℕ} (hx : 1 < x) (hc : 2 ≤ c) (hc4 : c ≤ 3)
    (h : x ^ n = c) : n = 1 ∧ x = c := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at h; omega
  have hn : n = 1 := by
    by_contra hne
    have h2 : 2 ≤ n := by omega
    have : 2 ^ 2 ≤ x ^ n :=
      le_trans (Nat.pow_le_pow_left hx 2) (Nat.pow_le_pow_right (by omega) h2)
    omega
  subst hn; simpa using h

/-- Reduction of the Catalan–Mihăilescu statement to the case of prime exponents. -/
theorem catalan_reduction_to_prime_exponents
    (H : ∀ x y p q : ℕ, 1 < x → 1 < y → p.Prime → q.Prime → x ^ p = y ^ q + 1 →
      x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) :
    CatalanMihailescuStatement := by
  intro x y p q hx hy hp hq h
  have hrp : (p.minFac).Prime := Nat.minFac_prime (by omega)
  have hsp : (q.minFac).Prime := Nat.minFac_prime (by omega)
  obtain ⟨p', hp'⟩ : p.minFac ∣ p := Nat.minFac_dvd p
  obtain ⟨q', hq'⟩ : q.minFac ∣ q := Nat.minFac_dvd q
  have hp'pos : 0 < p' := by
    rcases Nat.eq_zero_or_pos p' with h0 | h0
    · subst h0; simp at hp'; omega
    · exact h0
  have hq'pos : 0 < q' := by
    rcases Nat.eq_zero_or_pos q' with h0 | h0
    · subst h0; simp at hq'; omega
    · exact h0
  have hX : 1 < x ^ p' := Nat.one_lt_pow (by omega) hx
  have hY : 1 < y ^ q' := Nat.one_lt_pow (by omega) hy
  have key : (x ^ p') ^ p.minFac = (y ^ q') ^ q.minFac + 1 := by
    rw [← pow_mul, ← pow_mul, mul_comm p' p.minFac, mul_comm q' q.minFac, ← hp', ← hq']
    exact h
  obtain ⟨h1, h2, h3, h4⟩ := H _ _ _ _ hX hY hrp hsp key
  obtain ⟨hp'1, hx3⟩ := pow_eq_small hx (by omega) (by omega) h1
  obtain ⟨hq'1, hy2⟩ := pow_eq_small hy (by omega) (by omega) h3
  exact ⟨hx3, by rw [hp', h2, hp'1], hy2, by rw [hq', h4, hq'1]⟩

/-! ## Gaussian integer preliminaries -/

/-- The Gaussian unit `i`. -/
def gi : GaussianInt := ⟨0, 1⟩

/-- The imaginary part of a Gaussian integer, as an additive homomorphism. -/
def imHom : GaussianInt →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `eps m` is the imaginary part of `i ^ m`. -/
def eps (m : ℕ) : ℤ := (gi ^ m).im

lemma gi_sq : gi ^ 2 = -1 := by decide

private lemma neg_one_pow_im (n : ℕ) : (((-1 : GaussianInt)) ^ n).im = 0 := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]; rfl
  · rw [h.neg_one_pow]; rfl

lemma eps_of_even {m : ℕ} (h : Even m) : eps m = 0 := by
  obtain ⟨n, rfl⟩ := h
  have hn : n + n = 2 * n := by ring
  rw [eps, hn, pow_mul, gi_sq, neg_one_pow_im]

lemma eps_sq_of_odd {m : ℕ} (h : Odd m) : eps m ^ 2 = 1 := by
  obtain ⟨n, rfl⟩ := h
  have hpow : (gi ^ (2 * n + 1)) = ((-1 : GaussianInt)) ^ n * gi := by
    rw [pow_add, pow_mul, gi_sq, pow_one]
  rw [eps, hpow]
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]; norm_num [gi]
  · rw [h.neg_one_pow]; simp [gi]

lemma eps_eq_one_or_neg_one {m : ℕ} (h : Odd m) : eps m = 1 ∨ eps m = -1 := by
  have h1 := eps_sq_of_odd h
  have h2 : (eps m - 1) * (eps m + 1) = 0 := by nlinarith
  rcases mul_eq_zero.1 h2 with h' | h'
  · left; linarith
  · right; linarith

/-- Binomial expansion of the imaginary part of `(a + i) ^ r`. -/
lemma im_pow_add_gi (a : ℤ) (r : ℕ) :
    (((a : GaussianInt) + gi) ^ r).im
      = ∑ k ∈ Finset.range (r + 1), a ^ k * (r.choose k : ℤ) * eps (r - k) := by
  rw [add_pow]
  have hsum : (((∑ k ∈ Finset.range (r + 1),
        (a : GaussianInt) ^ k * gi ^ (r - k) * (r.choose k : GaussianInt))).im)
      = ∑ k ∈ Finset.range (r + 1),
          imHom ((a : GaussianInt) ^ k * gi ^ (r - k) * (r.choose k : GaussianInt)) :=
    map_sum imHom _ _
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro k _
  show ((a : GaussianInt) ^ k * gi ^ (r - k) * (r.choose k : GaussianInt)).im = _
  have h1 : ((a : GaussianInt)) ^ k = ((a ^ k : ℤ) : GaussianInt) := by push_cast; ring
  have h2 : ((r.choose k : GaussianInt)) = (((r.choose k : ℤ)) : GaussianInt) := by
    push_cast; ring
  rw [h1, h2]
  simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, eps]
  ring

/-! ## The 2-adic key lemma -/

private lemma choose_two_of_two_mul (j : ℕ) : (2 * j).choose 2 = j * (2 * j - 1) := by
  have h : 2 * j * (2 * j - 1) = 2 * (j * (2 * j - 1)) := by ring
  rw [Nat.choose_two_right, h, Nat.mul_div_cancel_left _ (by norm_num)]

/-- If `2 ^ e` divides `C(r, 2)` then it divides `C(r, 2 * j) * j`.  This is the key
comparison of `2`-adic valuations of binomial coefficients, coming from the identity
`C(r, 2j) * C(2j, 2) = C(r, 2) * C(r - 2, 2j - 2)`. -/
lemma pow_two_dvd_choose_mul {r j e : ℕ} (hj : 2 ≤ j)
    (he : 2 ^ e ∣ r.choose 2) : 2 ^ e ∣ r.choose (2 * j) * j := by
  have hid : r.choose (2 * j) * (2 * j).choose 2 = r.choose 2 * (r - 2).choose (2 * j - 2) :=
    Nat.choose_mul (by omega)
  rw [choose_two_of_two_mul] at hid
  have h1 : 2 ^ e ∣ r.choose (2 * j) * j * (2 * j - 1) := by
    rw [mul_assoc, hid]
    exact Dvd.dvd.mul_right he _
  have hcop : Nat.Coprime (2 ^ e) (2 * j - 1) := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  exact hcop.dvd_of_dvd_mul_right h1

/-- The `2`-adic estimate for the terms of index `≥ 2` in the binomial expansion. -/
lemma pow_two_dvd_term {r j v e : ℕ} (hv : 1 ≤ v) (hj : 2 ≤ j)
    (he : 2 ^ e ∣ r.choose 2) :
    2 ^ (2 * v + e + 1) ∣ r.choose (2 * j) * 2 ^ (2 * j * v) := by
  obtain ⟨t, j', hj', hjt⟩ := Nat.exists_eq_two_pow_mul_odd (n := j) (by omega)
  have hdvd : 2 ^ e ∣ r.choose (2 * j) * j := pow_two_dvd_choose_mul hj he
  have hcop : Nat.Coprime (2 ^ e) j' := by
    refine Nat.Coprime.pow_left _ ?_
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    rw [Nat.odd_iff] at hj'
    omega
  have hdvd2 : 2 ^ e ∣ r.choose (2 * j) * 2 ^ t := by
    refine hcop.dvd_of_dvd_mul_right ?_
    rw [mul_assoc, ← hjt]
    exact hdvd
  have htj : 2 ^ t ≤ j := Nat.le_of_dvd (by omega) ⟨j', hjt⟩
  have htlt : t < 2 ^ t := Nat.lt_two_pow_self
  have ht1 : t + 1 ≤ j := by omega
  have hineq : 2 * v + e + 1 ≤ e + (2 * j * v - t) := by
    have h2 : 2 * j * v = 2 * v * (j - 1) + 2 * v := by
      have hj1 : j - 1 + 1 = j := by omega
      nlinarith [hj1]
    have h1 : 2 * (j - 1) ≤ 2 * v * (j - 1) := by nlinarith [Nat.sub_le j 1]
    omega
  have hsum : t + (2 * j * v - t) = 2 * j * v := by
    have hle : t ≤ 2 * j * v := by nlinarith
    omega
  have h2 : 2 ^ e * 2 ^ (2 * j * v - t) ∣ (r.choose (2 * j) * 2 ^ t) * 2 ^ (2 * j * v - t) :=
    mul_dvd_mul_right hdvd2 _
  have h3 : (r.choose (2 * j) * 2 ^ t) * 2 ^ (2 * j * v - t)
      = r.choose (2 * j) * 2 ^ (2 * j * v) := by
    rw [mul_assoc (r.choose (2 * j)) (2 ^ t), ← pow_add, hsum]
  have h4 : (2:ℕ) ^ e * 2 ^ (2 * j * v - t) = 2 ^ (e + (2 * j * v - t)) := (pow_add 2 _ _).symm
  rw [h3, h4] at h2
  exact dvd_trans (pow_dvd_pow 2 hineq) h2

/-- For `a` even and nonzero and `r ≥ 3` odd, `(a + i) ^ r` cannot have imaginary part `±1`.

The imaginary part is `±(1 - C(r,2) a² + C(r,4) a⁴ - ⋯)`; reduction mod `4` forces the
alternating tail `- C(r,2) a² + C(r,4) a⁴ - ⋯` to vanish, which is impossible because the
term `C(r,2) a²` has strictly smaller `2`-adic valuation than all the later ones. -/
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

private lemma one_le_mul_self {n : ℤ} (h : n ≠ 0) : 1 ≤ n * n := by
  have h1 : 1 ≤ |n| := Int.one_le_abs (by omega)
  nlinarith [abs_mul_abs_self n]

/-- Every unit of `ℤ[i]` has order dividing `4`. -/
lemma unit_pow_four {u : GaussianInt} (hu : IsUnit u) : u ^ 4 = 1 := by
  have hn : u.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.2 hu
  have hnorm : u.norm = u.re * u.re + u.im * u.im := by rw [Zsqrtd.norm_def]; ring
  have hpos : (0:ℤ) ≤ u.norm := by
    rw [hnorm]; nlinarith [mul_self_nonneg u.re, mul_self_nonneg u.im]
  have h1 : u.re * u.re + u.im * u.im = 1 := by rw [← hnorm]; omega
  have hzero : u.re = 0 ∨ u.im = 0 := by
    by_contra hc
    push_neg at hc
    obtain ⟨h2, h3⟩ := hc
    have ha := one_le_mul_self h2
    have hb := one_le_mul_self h3
    omega
  have hsq : u ^ 2 = (((u.re * u.re - u.im * u.im : ℤ)) : GaussianInt) := by
    have hAB : u.re * u.im = 0 := by rcases hzero with h | h <;> simp [h]
    apply Zsqrtd.ext <;>
      simp only [pow_two, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] <;>
      nlinarith [hAB]
  have h4 : (u.re * u.re - u.im * u.im) ^ 2 = 1 := by
    rcases hzero with h | h <;> rw [h] at h1 ⊢ <;> nlinarith
  calc u ^ 4 = (u ^ 2) ^ 2 := by ring
  _ = (((u.re * u.re - u.im * u.im : ℤ)) : GaussianInt) ^ 2 := by rw [hsq]
  _ = 1 := by rw [← Int.cast_pow, h4]; norm_num

/-- If `Y` is even then `Y + i` and `Y - i` are coprime Gaussian integers. -/
lemma gauss_coprime {Y : ℤ} (hY : Even Y) :
    IsCoprime (⟨Y, 1⟩ : GaussianInt) (⟨Y, -1⟩ : GaussianInt) := by
  obtain ⟨m, rfl⟩ := hY
  have h2 : IsCoprime ((m + m) ^ 2 + 1 : ℤ) 2 := ⟨1, -(2 * m ^ 2), by ring⟩
  have h4 : IsCoprime ((m + m) ^ 2 + 1 : ℤ) 4 := by
    have h := h2.pow_right (n := 2); norm_num at h; exact h
  obtain ⟨A, B, hAB⟩ := h4
  set s : GaussianInt := ⟨m + m, 1⟩ with hs
  set t : GaussianInt := ⟨m + m, -1⟩ with ht
  have hst : s * t = ((((m + m) ^ 2 + 1 : ℤ)) : GaussianInt) := by
    simp only [hs, ht, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast,
      Zsqrtd.im_intCast]
    constructor <;> ring
  have hsub : (4 : GaussianInt) = -(s - t) ^ 2 := by
    simp only [hs, ht, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul, pow_two, Zsqrtd.re_neg,
      Zsqrtd.im_neg, Zsqrtd.re_sub, Zsqrtd.im_sub]
    constructor <;> ring_nf <;> rfl
  have hcast : ((A : GaussianInt)) * ((((m + m) ^ 2 + 1 : ℤ)) : GaussianInt)
      + ((B : GaussianInt)) * 4 = 1 := by
    have h := congrArg (fun n : ℤ => ((n : GaussianInt))) hAB
    push_cast at h
    push_cast
    linear_combination h
  rw [← hst, hsub] at hcast
  exact ⟨(A : GaussianInt) * t - (B : GaussianInt) * s + 2 * (B : GaussianInt) * t,
    -(B : GaussianInt) * t, by linear_combination hcast⟩

lemma znorm_pow (z : GaussianInt) (n : ℕ) : (z ^ n).norm = z.norm ^ n := by
  induction n with
  | zero => simp [Zsqrtd.norm_def]
  | succ k ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

/-- The core case of Lebesgue's theorem: odd exponent `r ≥ 3`. -/
theorem lebesgue_odd {r : ℕ} (hodd : Odd r) (hr : 3 ≤ r) (x y : ℕ) (hy : 0 < y) :
    x ^ r ≠ y ^ 2 + 1 := by
  intro h
  -- `y` is even
  have hyeven : Even y := by
    rcases Nat.even_or_odd y with he | ho
    · exact he
    obtain ⟨m, hm⟩ := ho
    exfalso
    subst hm
    obtain ⟨u, hu⟩ := Nat.even_mul_succ_self m
    have hexp : (2 * m + 1) ^ 2 + 1 = 8 * u + 2 := by
      have h1 : (2 * m + 1) ^ 2 + 1 = 4 * (m * (m + 1)) + 2 := by ring
      rw [hu] at h1; omega
    have hdvd2 : 2 ∣ x ^ r := ⟨4 * u + 1, by rw [h, hexp]; ring⟩
    have h2x : 2 ∣ x := Nat.Prime.dvd_of_dvd_pow Nat.prime_two hdvd2
    obtain ⟨c, rfl⟩ := h2x
    have h8 : (8 : ℕ) ∣ (2 * c) ^ r := by
      have h1 : (2:ℕ) ^ 3 ∣ 2 ^ r := pow_dvd_pow 2 hr
      have h2 : (2:ℕ) ^ r ∣ (2 * c) ^ r := ⟨c ^ r, by rw [mul_pow]⟩
      exact dvd_trans (by norm_num) (dvd_trans h1 h2)
    rw [h, hexp] at h8
    omega
  -- `x` is odd
  have hxodd : Odd x := by
    have hy2 : Even (y ^ 2) := Nat.even_pow.mpr ⟨hyeven, two_ne_zero⟩
    rcases Nat.even_or_odd x with he | ho
    · exfalso
      have hev : Even (x ^ r) := Nat.even_pow.mpr ⟨he, by omega⟩
      rw [Nat.even_iff] at hev hy2
      omega
    · exact ho
  -- pass to the Gaussian integers
  have hZ : (x : ℤ) ^ r = (y : ℤ) ^ 2 + 1 := by exact_mod_cast congrArg (Nat.cast (R := ℤ)) h
  have hYeven : Even ((y : ℤ)) := by exact_mod_cast hyeven
  set X : ℤ := (x : ℤ) with hXdef
  set Y : ℤ := (y : ℤ) with hYdef
  set s : GaussianInt := ⟨Y, 1⟩ with hs
  set t : GaussianInt := ⟨Y, -1⟩ with ht
  have hst : s * t = ((X : GaussianInt)) ^ r := by
    have h1 : s * t = (((Y ^ 2 + 1 : ℤ)) : GaussianInt) := by
      simp only [hs, ht, Zsqrtd.ext_iff, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_intCast,
        Zsqrtd.im_intCast]
      constructor <;> ring
    rw [h1, ← hZ]; push_cast; ring
  obtain ⟨d, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' (gauss_coprime hYeven) hst
  have hu4 : ((u : GaussianInt)) ^ 4 = 1 := unit_pow_four u.isUnit
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨w, hw⟩ := Nat.even_mul_succ_self m
  have hr2 : r * r = 8 * w + 1 := by
    subst hm
    have h1 : (2 * m + 1) * (2 * m + 1) = 4 * (m * (m + 1)) + 1 := by ring
    rw [hw] at h1; omega
  set z : GaussianInt := ((u : GaussianInt)) ^ r * d with hzdef
  have hz : z ^ r = s := by
    have h1 : z ^ r = ((u : GaussianInt)) ^ (r * r) * d ^ r := by
      rw [hzdef, mul_pow, ← pow_mul]
    rw [h1, hr2]
    have h8 : ((u : GaussianInt)) ^ (8 * w + 1) = (u : GaussianInt) := by
      have h2 : ((u : GaussianInt)) ^ 8 = 1 := by
        rw [show (8:ℕ) = 4 * 2 by norm_num, pow_mul, hu4, one_pow]
      rw [pow_add, pow_one, pow_mul, h2, one_pow, one_mul]
    rw [h8, mul_comm]
    exact hu
  have hodd' : Odd r := ⟨m, hm⟩
  have hstar : (star z) ^ r = t := by
    rw [← star_pow, hz, hs, ht]
    apply Zsqrtd.ext <;> simp
  -- the imaginary part of `z` is `±1`
  have hsubst : s - t = (⟨0, 2⟩ : GaussianInt) := by
    rw [hs, ht]; apply Zsqrtd.ext <;> simp <;> ring
  have hzs : z - star z = (⟨0, 2 * z.im⟩ : GaussianInt) := by
    apply Zsqrtd.ext <;> simp <;> ring
  have hdvd : (⟨0, 2 * z.im⟩ : GaussianInt) ∣ (⟨0, 2⟩ : GaussianInt) := by
    have h1 := sub_dvd_pow_sub_pow z (star z) r
    rw [hz, hstar, hsubst, hzs] at h1
    exact h1
  obtain ⟨c, hc⟩ := hdvd
  have hnormdvd : (4 * z.im ^ 2 : ℤ) ∣ 4 := by
    refine ⟨c.norm, ?_⟩
    have h1 := congrArg Zsqrtd.norm hc
    rw [Zsqrtd.norm_mul] at h1
    simp only [Zsqrtd.norm_def] at h1 ⊢
    linarith [h1]
  have hb : z.im = 1 ∨ z.im = -1 := by
    have h1 : (4:ℤ) * z.im ^ 2 ∣ 4 * 1 := by simpa using hnormdvd
    have h2 : z.im ^ 2 ∣ 1 := (mul_dvd_mul_iff_left (by norm_num : (4:ℤ) ≠ 0)).mp h1
    have h3 : z.im ∣ 1 := dvd_trans (dvd_pow_self z.im two_ne_zero) h2
    exact Int.isUnit_iff.mp (isUnit_of_dvd_one h3)
  -- the real part of `z` is even and nonzero
  have hnormz : z.norm = z.re ^ 2 + 1 := by
    rcases hb with h1 | h1 <;> rw [Zsqrtd.norm_def, h1] <;> ring
  have hnorms : s.norm = X ^ r := by rw [hs, Zsqrtd.norm_def, hZ]; ring
  have hpow : (z.re ^ 2 + 1) ^ r = X ^ r := by rw [← hnormz, ← znorm_pow, hz, hnorms]
  have hXeq : z.re ^ 2 + 1 = X := (Odd.strictMono_pow (R := ℤ) hodd').injective hpow
  have hXodd : Odd X := by rw [hXdef]; exact_mod_cast hxodd
  have hare : Even z.re := by
    rcases Int.even_or_odd z.re with he | ho
    · exact he
    · exfalso
      obtain ⟨k, hk⟩ := ho
      obtain ⟨j, hj⟩ := hXodd
      rw [hk] at hXeq
      have h1 : X = 2 * (2 * (k * k + k) + 1) := by rw [← hXeq]; ring
      generalize (k * k + k) = n at h1
      omega
  have hne : z.re ≠ 0 := by
    intro h0
    rw [h0] at hXeq
    have hX1 : X = 1 := by omega
    rw [hX1, one_pow] at hZ
    have hY0 : Y = 0 := by nlinarith [sq_nonneg Y]
    rw [hYdef] at hY0
    omega
  -- conclude with the key lemma
  rcases hb with h1 | h1
  · have hzeq : ((z.re : GaussianInt)) + gi = z := by
      apply Zsqrtd.ext <;> simp [gi, h1]
    have him : ((((z.re : GaussianInt)) + gi) ^ r).im = 1 := by rw [hzeq, hz, hs]
    exact im_pow_add_gi_ne_pm_one hodd' hr hare hne (Or.inl rfl) him
  · have hzeq : ((z.re : GaussianInt)) + gi = star z := by
      apply Zsqrtd.ext <;> simp [gi, h1]
    have him : ((((z.re : GaussianInt)) + gi) ^ r).im = -1 := by rw [hzeq, hstar, ht]
    exact im_pow_add_gi_ne_pm_one hodd' hr hare hne (Or.inr rfl) him

/-- **Lebesgue's theorem (1850)**: for `p ≥ 2` and `y ≥ 1`, `x ^ p = y ^ 2 + 1` is impossible;
that is, `1` is never the difference of a perfect power and a nonzero perfect square. -/
theorem lebesgue {p : ℕ} (hp : 2 ≤ p) (x y : ℕ) (hy : 0 < y) : x ^ p ≠ y ^ 2 + 1 := by
  intro h
  rcases Nat.even_or_odd p with he | ho
  · obtain ⟨k, hk⟩ := he
    have hk1 : 1 ≤ k := by omega
    have hX : (x ^ k) ^ 2 = y ^ 2 + 1 := by rw [← pow_mul, ← h]; congr 1; omega
    set X := x ^ k with hXdef
    have hXy : y < X := by nlinarith [sq_nonneg X]
    nlinarith
  · exact lebesgue_odd ho (by rcases ho with ⟨m, hm⟩; omega) x y hy h

/-! ## The target -/

/-- **Catalan–Mihăilescu, the even-exponent case.**  `3 ^ 2 = 2 ^ 3 + 1` is a solution of
Catalan's equation, and there is no solution `x ^ p = y ^ q + 1` (with `x, y, p, q > 1`)
in which the exponent `q` is even.  (In Mihăilescu's theorem the unique solution has
`q = 3`, so this is a genuine — and unconditional — case of the full statement; the case
of even `q` is Lebesgue's theorem of 1850.) -/
theorem Catalan_Mihailescu :
    (3 ^ 2 = 2 ^ 3 + 1) ∧
      ∀ x y p q : ℕ, 1 < x → 1 < y → 1 < p → 1 < q → Even q → x ^ p ≠ y ^ q + 1 := by
  refine ⟨by norm_num, ?_⟩
  intro x y p q hx hy hp hq hqe h
  obtain ⟨m, hm⟩ := hqe
  subst hm
  have h2 : x ^ p = (y ^ m) ^ 2 + 1 := by
    rw [← pow_mul, show m * 2 = m + m from by ring]; exact h
  exact lebesgue (by omega) x (y ^ m) (by positivity) h2

end Frontier

