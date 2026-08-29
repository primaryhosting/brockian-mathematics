import Mathlib
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

/-!
# Superperfect numbers and the Mersenne connection

For `σ(n) = ∑_{d ∣ n} d` the sum of **all** divisors of `n`, a positive integer is
**superperfect** when applying `σ` twice returns twice the number:

    σ(σ(n)) = 2n.

This is the "second-iterate" analogue of a perfect number (`σ(n) = 2n`). The structure
of the *even* superperfect numbers is completely understood, and it ties directly to the
Mersenne primes:

> **Kanold / Suryanarayana.** The even superperfect numbers are exactly the powers
> `2^{p−1}` for which `2^p − 1` is a (Mersenne) prime — e.g. `2, 4, 16, 64, …`.

whereas the *odd* case is a genuine open problem, parallel to the odd perfect number
question:

> **OPEN.** No odd superperfect number is known, and it is unknown whether one exists.

## What is a theorem here vs. what is open

Proved below (kernel-verified: no `sorry` / `admit` / `native_decide` / added axiom):

* concrete instances `superperfect_2, superperfect_4, superperfect_16, superperfect_64`
  (e.g. `σ(σ(64)) = σ(127) = 128 = 2·64`);
* the **structural direction** `superperfect_two_pow_of_mersenne_prime`: if `2 ≤ p` and
  `mersenne p = 2^p − 1` is prime, then `2^{p−1}` is superperfect. The proof runs
  `σ(2^{p−1}) = 2^p − 1 = mersenne p`, then (as `mersenne p` is prime)
  `σ(mersenne p) = mersenne p + 1 = 2^p = 2·2^{p−1}`;
* a non-example `six_not_superperfect` (`σ(σ(6)) = σ(12) = 28 ≠ 12`).

What is genuinely **open** — whether any **odd** superperfect number exists — is recorded
only as an unproven `def` `OddSuperperfectExists : Prop`. It is **neither asserted nor
denied** anywhere in this file.

## References
* Superperfect number: <https://en.wikipedia.org/wiki/Superperfect_number>
* D. Suryanarayana, *Super perfect numbers*, Elem. Math. 24 (1969), 16–17.
-/

namespace Brockian.SuperperfectNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Sum of **all** divisors of `n` (the arithmetic `σ₁`, counting `n` itself). -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- **Superperfect**: applying `σ` twice doubles `n`, i.e. `σ(σ(n)) = 2n`. -/
def Superperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 (sigma1 n) = 2 * n

/-- OPEN: does an **odd** superperfect number exist? **None is known** — parallel to the
odd perfect number problem. Recorded as an unproven `def`; this file neither asserts nor
denies it. -/
def OddSuperperfectExists : Prop := ∃ n : ℕ, Odd n ∧ Superperfect n

/-! ## σ-helpers -/

/-- `σ(2^k) = 2^{k+1} − 1` (the Mersenne value `2^{k+1}−1`), via the geometric-sum identity
for the divisor sum of a power of two. -/
theorem sigma_two_pow (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  simp_rw [sigma_one_apply, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- For a prime `q`, `σ(q) = 1 + q` (its only divisors are `1` and `q`). -/
theorem sigma1_prime {q : ℕ} (hq : q.Prime) : sigma1 q = 1 + q := by
  rw [sigma1, hq.divisors, Finset.sum_pair hq.one_lt.ne]

/-! ## FLAGSHIP — the Mersenne connection -/

/-- **FLAGSHIP.** If `2 ≤ p` and `mersenne p = 2^p − 1` is prime, then `2^{p−1}` is
superperfect: `σ(σ(2^{p−1})) = σ(2^p − 1) = 2^p = 2·2^{p−1}`. This is the structural
theorem tying the even superperfect numbers to the Mersenne primes. -/
theorem superperfect_two_pow_of_mersenne_prime {p : ℕ} (hp : 2 ≤ p)
    (hm : (mersenne p).Prime) : Superperfect (2 ^ (p - 1)) := by
  refine ⟨by positivity, ?_⟩
  have hk : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  -- First iterate: σ(2^{p−1}) = mersenne p = 2^p − 1.
  have h1 : sigma1 (2 ^ (p - 1)) = mersenne p := by
    rw [show sigma1 (2 ^ (p - 1)) = σ 1 (2 ^ (p - 1)) from (sigma_one_apply _).symm,
      sigma_two_pow, hk]
    rfl
  rw [h1, sigma1_prime hm]
  -- Second iterate: σ(mersenne p) = 1 + (2^p − 1) = 2^p = 2·2^{p−1}.
  have hpow : 2 ^ p = 2 * 2 ^ (p - 1) := by
    conv_lhs => rw [← hk, pow_succ]
    ring
  have hge : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  unfold mersenne
  omega

/-! ## FLAGSHIP — concrete verified instances

Each `2^{p−1}` below corresponds to a Mersenne prime `2^p−1`:
`p=2→2^1=2` (`M=3`), `p=3→2^2=4` (`M=7`), `p=5→2^4=16` (`M=31`), `p=7→2^6=64` (`M=127`). -/

/-- `σ(σ(2)) = σ(3) = 4 = 2·2`. -/
theorem superperfect_2 : Superperfect 2 := ⟨by norm_num, by decide⟩

/-- `σ(σ(4)) = σ(7) = 8 = 2·4`. -/
theorem superperfect_4 : Superperfect 4 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 8000 in
/-- `σ(σ(16)) = σ(31) = 32 = 2·16`. -/
theorem superperfect_16 : Superperfect 16 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
/-- `σ(σ(64)) = σ(127) = 128 = 2·64` (`127` is the Mersenne prime `2^7−1`). -/
theorem superperfect_64 : Superperfect 64 := ⟨by norm_num, by decide⟩

/-! ## A non-example -/

set_option maxRecDepth 8000 in
/-- `6` is **not** superperfect: `σ(σ(6)) = σ(12) = 28 ≠ 12 = 2·6`. -/
theorem six_not_superperfect : ¬ Superperfect 6 := by unfold Superperfect; decide


/-- `σ(2^k) = 2^(k+1) - 1`. -/
lemma sigma1_two_pow (k : ℕ) : sigma1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  unfold sigma1
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      rw [pow_succ 2 (n + 1)]
      omega


/-- If `σ(m) = m + 1` then `m` is prime. -/
lemma prime_of_sigma1_eq_succ {m : ℕ} (hm : sigma1 m = m + 1) : Nat.Prime m := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp [sigma1] at hm
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp [sigma1] at hm
  have h2 : 2 ≤ m := by omega
  have hmemsub : ∀ d, d ∣ m → d = 1 ∨ d = m := by
    intro d hd
    by_contra hcon
    push_neg at hcon
    obtain ⟨hd1, hdm⟩ := hcon
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hm0 (Nat.eq_zero_of_zero_dvd hd)
    have hd2 : 2 ≤ d := by omega
    have hsub : ({1, d, m} : Finset ℕ) ⊆ m.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Nat.mem_divisors.mpr ⟨one_dvd m, hm0⟩
      · exact Nat.mem_divisors.mpr ⟨hd, hm0⟩
      · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hm0⟩
    have hsum : ∑ x ∈ ({1, d, m} : Finset ℕ), x ≤ sigma1 m :=
      Finset.sum_le_sum_of_subset hsub
    have hcard : ∑ x ∈ ({1, d, m} : Finset ℕ), x = 1 + d + m := by
      rw [Finset.sum_insert (by simp [Ne.symm hd1, Ne.symm hm1]), Finset.sum_insert (by simp [hdm]),
        Finset.sum_singleton]
      ring
    omega
  exact Nat.prime_def.mpr ⟨h2, hmemsub⟩


theorem mersenne_prime_of_superperfect_two_pow {k : ℕ}
    (h : Superperfect (2 ^ k)) : Nat.Prime (2 ^ (k + 1) - 1) := by
  obtain ⟨-, h⟩ := h
  rw [sigma1_two_pow k] at h
  apply prime_of_sigma1_eq_succ
  have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  rw [h, pow_succ 2 k]
  omega


/-- **Characterisation.** A power of two `2^k` is superperfect exactly when the Mersenne
number `2^{k+1} − 1` is prime. -/
theorem superperfect_two_pow_iff_mersenne_prime (k : ℕ) :
    Superperfect (2 ^ k) ↔ Nat.Prime (2 ^ (k + 1) - 1) := by
  refine ⟨mersenne_prime_of_superperfect_two_pow, fun hp => ?_⟩
  have hk : k ≠ 0 := by
    rintro rfl
    norm_num at hp
  have h2 : 2 ≤ k + 1 := by omega
  have hm : (mersenne (k + 1)).Prime := hp
  simpa using superperfect_two_pow_of_mersenne_prime h2 hm


/-- Any two distinct divisors of `n` give a lower bound for `σ(n)`. -/
lemma add_le_sigma1 {n a b : ℕ} (hn : n ≠ 0) (ha : a ∣ n) (hb : b ∣ n) (hab : a ≠ b) :
    a + b ≤ sigma1 n := by
  have hsub : ({a, b} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisors.mpr ⟨ha, hn⟩
    · exact Nat.mem_divisors.mpr ⟨hb, hn⟩
  calc a + b = ∑ x ∈ ({a, b} : Finset ℕ), x := (Finset.sum_pair (f := fun x => x) hab).symm
    _ ≤ sigma1 n := Finset.sum_le_sum_of_subset hsub


/-- `n ≤ σ(n)`, as `n` is one of its own divisors. -/
lemma self_le_sigma1 {n : ℕ} (hn : n ≠ 0) : n ≤ sigma1 n :=
  Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n hn)


/-- Every divisor of an odd number is odd. -/
lemma odd_of_dvd_odd {n d : ℕ} (hodd : Odd n) (hd : d ∣ n) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    have h2 : (2 : ℕ) ∣ n := he.two_dvd.trans hd
    rw [Nat.odd_iff] at hodd
    omega
  · exact ho


/-- For odd `n` which is not a perfect square, `σ(n)` is even: the involution
`d ↦ n / d` on the divisors of `n` has no fixed point, and pairs up odd divisors. -/
lemma even_sigma1_of_odd_of_not_isSquare {n : ℕ} (hodd : Odd n) (hn : 0 < n)
    (hsq : ¬ IsSquare n) : Even (sigma1 n) := by
  have hn0 : n ≠ 0 := hn.ne'
  rw [← ZMod.natCast_eq_zero_iff_even]
  rw [sigma1, Nat.cast_sum]
  refine Finset.sum_involution (fun d _ => n / d) ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have h1 : ((d : ℕ) : ZMod 2) = 1 :=
      ZMod.natCast_eq_one_iff_odd.mpr (odd_of_dvd_odd hodd hdvd)
    have h2 : ((n / d : ℕ) : ZMod 2) = 1 :=
      ZMod.natCast_eq_one_iff_odd.mpr (odd_of_dvd_odd hodd (Nat.div_dvd_of_dvd hdvd))
    rw [h1, h2]
    decide
  · intro d hd _
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    intro hcon
    have hcon' : n / d = d := hcon
    have hnd : n = d * d := by
      conv_lhs => rw [← Nat.div_mul_cancel hdvd, hcon']
    exact hsq ⟨d, hnd⟩
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn0⟩
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    exact Nat.div_div_self hdvd hn0


/-- Multiplicativity of `σ` in the shape needed below: `σ(2^a·u) = (2^{a+1}−1)·σ(u)` for
odd `u`. -/
lemma sigma1_two_pow_mul {a u : ℕ} (hu : Odd u) :
    sigma1 (2 ^ a * u) = (2 ^ (a + 1) - 1) * sigma1 u := by
  have hcop : Nat.Coprime (2 ^ a) u := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hu)
  have h : sigma1 (2 ^ a * u) = sigma1 (2 ^ a) * sigma1 u := by
    simp only [sigma1, ← sigma_one_apply]
    exact isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [h, sigma1_two_pow]


/-- **Kanold.** An odd superperfect number must be a perfect square: no odd non-square is
superperfect. -/
theorem not_superperfect_odd_of_not_sq {n : ℕ} (hodd : Odd n) (hn : 0 < n)
    (hsq : ¬ IsSquare n) : ¬ Superperfect n := by
  rintro ⟨-, hS⟩
  have hn0 : n ≠ 0 := hn.ne'
  have hmpos : 0 < sigma1 n := lt_of_lt_of_le hn (self_le_sigma1 hn0)
  have heven : Even (sigma1 n) := even_sigma1_of_odd_of_not_isSquare hodd hn hsq
  obtain ⟨a, u, hu, hmu⟩ := Nat.exists_eq_two_pow_mul_odd hmpos.ne'
  have hu0 : 0 < u := hu.pos
  -- `a ≥ 1` since `σ(n)` is even and `u` is odd.
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exfalso
      rw [pow_zero, one_mul] at hmu
      rw [hmu, Nat.even_iff] at heven
      rw [Nat.odd_iff] at hu
      omega
    · exact h
  set d : ℕ := 2 ^ (a + 1) - 1 with hdd
  have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
  have h2a : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
  have hd1 : 1 ≤ d := by
    have : 2 ≤ 2 ^ (a + 1) := by omega
    omega
  have hdodd : Odd d := by
    have : 2 ≤ 2 ^ (a + 1) := by omega
    rw [Nat.odd_iff, hdd]
    have h4 : 4 ≤ 2 ^ (a + 1) := by
      calc (4 : ℕ) = 2 * 2 := by norm_num
        _ ≤ 2 * 2 ^ a := by omega
        _ = 2 ^ (a + 1) := hpow.symm
    have hev : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (Nat.succ_ne_zero a)
    omega
  -- the σ-equation, split off the 2-part
  have hkey : d * sigma1 u = 2 * n := by
    rw [← hS, hmu, sigma1_two_pow_mul hu]
  -- `d ∣ n`
  have hdn : d ∣ n := by
    have hdvd : d ∣ 2 * n := ⟨sigma1 u, hkey.symm⟩
    have hcop : Nat.Coprime d 2 := Nat.coprime_two_right.mpr hdodd
    exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)
  obtain ⟨c, hc⟩ := hdn
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · simp [hc] at hn0
    · exact h
  -- `n` and `c = n / d` are distinct divisors of `n`, so `σ(n) ≥ n + c`
  have hcd : c ∣ n := ⟨d, by rw [hc]; ring⟩
  have hne : n ≠ c := by
    intro h
    have : d * c = 1 * c := by rw [← hc, h, one_mul]
    have := Nat.eq_of_mul_eq_mul_right hc0 this
    have h3 : 3 ≤ d := by
      have : 4 ≤ 2 ^ (a + 1) := by
        calc (4 : ℕ) = 2 * 2 := by norm_num
          _ ≤ 2 * 2 ^ a := by omega
          _ = 2 ^ (a + 1) := hpow.symm
      omega
    omega
  have hbound : n + c ≤ sigma1 n := add_le_sigma1 hn0 dvd_rfl hcd hne
  -- combine: `2^a * u ≥ (d+1) * c = 2^{a+1} * c`, hence `u ≥ 2c = σ(u)`
  have hstep : 2 ^ (a + 1) * c ≤ 2 ^ a * u := by
    have : (d + 1) * c ≤ sigma1 n := by
      rw [add_mul, one_mul, ← hc]
      exact hbound
    have hd1' : d + 1 = 2 ^ (a + 1) := by
      have : 2 ≤ 2 ^ (a + 1) := by omega
      omega
    rw [hd1'] at this
    rw [← hmu]
    exact this
  have hu2c : 2 * c ≤ u := by
    have h2 : 2 ^ a * (2 * c) ≤ 2 ^ a * u := by
      calc 2 ^ a * (2 * c) = 2 ^ (a + 1) * c := by ring
        _ ≤ 2 ^ a * u := hstep
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  have hsig : sigma1 u = 2 * c := by
    have h2 : d * sigma1 u = d * (2 * c) := by
      rw [hkey, hc]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  -- but `σ(u) ≥ u`, forcing `u = 2c`, and then `u = 1` is impossible
  have hle : u ≤ sigma1 u := self_le_sigma1 hu0.ne'
  have hueq : u = 2 * c := by omega
  have hu1 : u ≠ 1 := by omega
  have : 1 + u ≤ sigma1 u := add_le_sigma1 hu0.ne' (one_dvd u) dvd_rfl (fun h => hu1 h.symm)
  omega


/-- An odd prime is not superperfect: it is odd, positive, and (being prime) not a
perfect square, so `not_superperfect_odd_of_not_sq` applies. -/
theorem not_superperfect_odd_prime {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) :
    ¬ Superperfect p := by
  have hodd : Odd p := hp.odd_of_ne_two hne
  have hsq : ¬ IsSquare p := by
    rintro ⟨k, hk⟩
    have hkd : k ∣ p := ⟨k, hk⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp k hkd) with rfl | rfl
    · simp at hk
      exact hp.ne_one hk
    · have h2 : k * 1 = k * k := by rw [mul_one]; exact hk
      have := Nat.eq_of_mul_eq_mul_left hp.pos h2
      exact hp.ne_one this.symm
  exact not_superperfect_odd_of_not_sq hodd hp.pos hsq


/-- If `n` is an odd superperfect number, then `σ(n)` is odd.

The argument is the (Kanold) descent used in `not_superperfect_odd_of_not_sq`, run
directly from the assumption that `σ(n)` is even: writing `σ(n) = 2^a · u` with `u` odd
and `a ≥ 1`, the odd factor `d = 2^{a+1} − 1 ≥ 3` divides `n`, so `n` and `c = n/d` are
distinct divisors of `n`; this forces `σ(u) = 2c ≤ u`, contradicting `1 + u ≤ σ(u)`. -/
theorem odd_sigma1_of_superperfect_odd {n : ℕ} (hodd : Odd n) (hn : 0 < n)
    (h : Superperfect n) : Odd (sigma1 n) := by
  by_contra hcon
  rw [Nat.not_odd_iff_even] at hcon
  obtain ⟨-, hS⟩ := h
  have hn0 : n ≠ 0 := hn.ne'
  have hmpos : 0 < sigma1 n := lt_of_lt_of_le hn (self_le_sigma1 hn0)
  have heven : Even (sigma1 n) := hcon
  obtain ⟨a, u, hu, hmu⟩ := Nat.exists_eq_two_pow_mul_odd hmpos.ne'
  have hu0 : 0 < u := hu.pos
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · exfalso
      rw [pow_zero, one_mul] at hmu
      rw [hmu, Nat.even_iff] at heven
      rw [Nat.odd_iff] at hu
      omega
    · exact hpos
  set d : ℕ := 2 ^ (a + 1) - 1 with hdd
  have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
  have h2a : 2 ≤ 2 ^ a := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
  have hd1 : 1 ≤ d := by
    have : 2 ≤ 2 ^ (a + 1) := by omega
    omega
  have hdodd : Odd d := by
    have : 2 ≤ 2 ^ (a + 1) := by omega
    rw [Nat.odd_iff, hdd]
    have h4 : 4 ≤ 2 ^ (a + 1) := by
      calc (4 : ℕ) = 2 * 2 := by norm_num
        _ ≤ 2 * 2 ^ a := by omega
        _ = 2 ^ (a + 1) := hpow.symm
    have hev : 2 ∣ 2 ^ (a + 1) := dvd_pow_self 2 (Nat.succ_ne_zero a)
    omega
  have hkey : d * sigma1 u = 2 * n := by
    rw [← hS, hmu, sigma1_two_pow_mul hu]
  have hdn : d ∣ n := by
    have hdvd : d ∣ 2 * n := ⟨sigma1 u, hkey.symm⟩
    have hcop : Nat.Coprime d 2 := Nat.coprime_two_right.mpr hdodd
    exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)
  obtain ⟨c, hc⟩ := hdn
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hpos
    · simp [hc] at hn0
    · exact hpos
  have hcd : c ∣ n := ⟨d, by rw [hc]; ring⟩
  have hne : n ≠ c := by
    intro heq
    have hmul : d * c = 1 * c := by rw [← hc, heq, one_mul]
    have := Nat.eq_of_mul_eq_mul_right hc0 hmul
    have h3 : 3 ≤ d := by
      have : 4 ≤ 2 ^ (a + 1) := by
        calc (4 : ℕ) = 2 * 2 := by norm_num
          _ ≤ 2 * 2 ^ a := by omega
          _ = 2 ^ (a + 1) := hpow.symm
      omega
    omega
  have hbound : n + c ≤ sigma1 n := add_le_sigma1 hn0 dvd_rfl hcd hne
  have hstep : 2 ^ (a + 1) * c ≤ 2 ^ a * u := by
    have hle' : (d + 1) * c ≤ sigma1 n := by
      rw [add_mul, one_mul, ← hc]
      exact hbound
    have hd1' : d + 1 = 2 ^ (a + 1) := by
      have : 2 ≤ 2 ^ (a + 1) := by omega
      omega
    rw [hd1'] at hle'
    rw [← hmu]
    exact hle'
  have hu2c : 2 * c ≤ u := by
    have h2 : 2 ^ a * (2 * c) ≤ 2 ^ a * u := by
      calc 2 ^ a * (2 * c) = 2 ^ (a + 1) * c := by ring
        _ ≤ 2 ^ a * u := hstep
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  have hsig : sigma1 u = 2 * c := by
    have h2 : d * sigma1 u = d * (2 * c) := by
      rw [hkey, hc]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h2
  have hle : u ≤ sigma1 u := self_le_sigma1 hu0.ne'
  have hueq : u = 2 * c := by omega
  have hu1 : u ≠ 1 := by omega
  have : 1 + u ≤ sigma1 u := add_le_sigma1 hu0.ne' (one_dvd u) dvd_rfl (fun h => hu1 h.symm)
  omega


/-- No odd number below `100` is superperfect. By Kanold's theorem an odd superperfect
number is a perfect square, so only `1, 9, 25, 49, 81` need checking, and each fails. -/
theorem no_odd_superperfect_lt_hundred (n : ℕ) (hn : n < 100) (hodd : Odd n) :
    ¬ Superperfect n := by
  intro hS
  have hn0 : 0 < n := hodd.pos
  by_cases hsq : IsSquare n
  · obtain ⟨k, hk⟩ := hsq
    subst hk
    have hk10 : k < 10 := by nlinarith
    rw [Nat.odd_iff] at hodd
    obtain ⟨-, hS2⟩ := hS
    interval_cases k <;> revert hodd hS2 <;> decide
  · exact not_superperfect_odd_of_not_sq hodd hn0 hsq hS


/-- For an odd perfect square `n = k * k`, the divisor sum `σ(n)` is odd: the involution
`d ↦ n / d` pairs up the divisors other than `k`, and every divisor is odd. -/
lemma odd_sigma1_of_odd_isSquare {n : ℕ} (hodd : Odd n) (hn : 0 < n) (hsq : IsSquare n) :
    Odd (sigma1 n) := by
  obtain ⟨k, hk⟩ := hsq
  have hn0 : n ≠ 0 := hn.ne'
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp [hk] at hn0
  have hkdvd : k ∣ n := ⟨k, hk⟩
  have hkmem : k ∈ n.divisors := Nat.mem_divisors.mpr ⟨hkdvd, hn0⟩
  have hnk : n / k = k := by
    rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk0)]
  have hkodd : Odd k := odd_of_dvd_odd hodd hkdvd
  -- the divisors other than `k` pair up under `d ↦ n / d`
  have heven : Even (∑ d ∈ n.divisors.erase k, d) := by
    rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
    refine Finset.sum_involution (fun d _ => n / d) ?_ ?_ ?_ ?_
    · intro d hd
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)
      have h1 : ((d : ℕ) : ZMod 2) = 1 :=
        ZMod.natCast_eq_one_iff_odd.mpr (odd_of_dvd_odd hodd hdvd)
      have h2 : ((n / d : ℕ) : ZMod 2) = 1 :=
        ZMod.natCast_eq_one_iff_odd.mpr (odd_of_dvd_odd hodd (Nat.div_dvd_of_dvd hdvd))
      rw [h1, h2]
      decide
    · intro d hd _
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)
      have hdk : d ≠ k := Finset.ne_of_mem_erase hd
      intro hcon
      have hcon' : n / d = d := hcon
      have hnd : n = d * d := by
        conv_lhs => rw [← Nat.div_mul_cancel hdvd, hcon']
      have hdk2 : d * d = k * k := by rw [← hnd, hk]
      exact hdk (Nat.mul_self_inj.mp hdk2)
    · intro d hd
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)
      have hdk : d ≠ k := Finset.ne_of_mem_erase hd
      refine Finset.mem_erase.mpr ⟨?_, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn0⟩⟩
      intro hcon
      have hcon' : n / d = k := hcon
      have hdd' := Nat.div_div_self hdvd hn0
      rw [hcon', hnk] at hdd'
      exact hdk hdd'.symm
    · intro d hd
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (Finset.mem_of_mem_erase hd)
      exact Nat.div_div_self hdvd hn0
  have hsplit : sigma1 n = k + ∑ d ∈ n.divisors.erase k, d := by
    rw [sigma1, ← Finset.add_sum_erase _ _ hkmem]
  rw [hsplit]
  exact hkodd.add_even heven


/-- **Characterisation of the parity of `σ` on odd numbers.** For odd `n > 0`, the divisor
sum `σ(n)` is odd exactly when `n` is a perfect square. -/
theorem odd_sigma1_iff_isSquare_of_odd {n : ℕ} (hodd : Odd n) (hn : 0 < n) :
    Odd (sigma1 n) ↔ IsSquare n := by
  refine ⟨fun h => ?_, fun h => odd_sigma1_of_odd_isSquare hodd hn h⟩
  by_contra hsq
  have := even_sigma1_of_odd_of_not_isSquare hodd hn hsq
  rw [Nat.odd_iff] at h
  rw [Nat.even_iff] at this
  omega

end Brockian.SuperperfectNumbers
