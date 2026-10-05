import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The set of `abc`-exceptions for a parameter `ε`: coprime triples `a + b = c` of positive
naturals with `rad (a * b * c) ^ (1 + ε) < c`. -/
def AbcExceptions (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t : ℕ × ℕ × ℕ | 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧ Nat.Coprime t.1 t.2.1 ∧
    ((rad (t.1 * t.2.1 * t.2.2) : ℝ)) ^ (1 + ε) < (t.2.2 : ℝ)}

/-- **The abc conjecture**: for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive naturals with `c > rad (a * b * c) ^ (1 + ε)`. -/
def AbcConjecture : Prop := ∀ ε : ℝ, 0 < ε → (AbcExceptions ε).Finite

/-! ### Basic facts about the radical -/

lemma rad_pos {n : ℕ} : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma one_le_rad {n : ℕ} : 1 ≤ rad n := rad_pos

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : rad (a * b) ≤ rad a * rad b := by
  classical
  have h : rad (a * b) * (∏ p ∈ a.primeFactors ∩ b.primeFactors, p) = rad a * rad b := by
    unfold rad
    rw [Nat.primeFactors_mul ha hb]
    exact Finset.prod_union_inter
  have hpos : 0 < ∏ p ∈ a.primeFactors ∩ b.primeFactors, p :=
    Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_inter_left hp)).pos
  calc rad (a * b) ≤ rad (a * b) * (∏ p ∈ a.primeFactors ∩ b.primeFactors, p) :=
        Nat.le_mul_of_pos_right _ hpos
    _ = rad a * rad b := h

lemma rad_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : rad (p ^ k) = p := by
  unfold rad
  rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton]

/-- The radical is at most twice the odd part of `n`. -/
lemma rad_le_two_mul_odd_part (x : ℕ) :
    rad x ≤ 2 * ∏ p ∈ x.primeFactors \ {2}, p := by
  classical
  by_cases h2 : 2 ∈ x.primeFactors
  · have : rad x = 2 * ∏ p ∈ x.primeFactors.erase 2, p := (Finset.mul_prod_erase _ _ h2).symm
    rw [this, Finset.sdiff_singleton_eq_erase]
  · have hs : x.primeFactors \ {2} = x.primeFactors := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem h2]
    rw [hs]
    exact Nat.le_mul_of_pos_left _ (by norm_num)

/-- If `2 ^ k ∣ x` then `2 ^ k * rad x ≤ 2 * x`. -/
lemma two_pow_mul_rad_le {x k : ℕ} (hx : x ≠ 0) (hdvd : 2 ^ k ∣ x) :
    2 ^ k * rad x ≤ 2 * x := by
  classical
  set K := x.factorization 2 with hK
  have hkK : k ≤ K := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hx).mp hdvd
  set m := x / 2 ^ K with hm
  have hxm : 2 ^ K * m = x := Nat.ordProj_mul_ordCompl_eq_self x 2
  set r' := ∏ p ∈ x.primeFactors \ {2}, p with hr'
  have hr'dvdrad : r' ∣ rad x :=
    Finset.prod_dvd_prod_of_subset _ _ _ Finset.sdiff_subset
  have hr'dvd : r' ∣ x := hr'dvdrad.trans (rad_dvd x)
  have hr'cop : Nat.Coprime r' (2 ^ K) := by
    refine Nat.Coprime.pow_right _ ?_
    refine Nat.Coprime.prod_left ?_
    intro p hp
    rw [Finset.mem_sdiff] at hp
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp.1) Nat.prime_two).mpr
      (by simpa using hp.2)
  have hr'm : r' ∣ m := hr'cop.dvd_of_dvd_mul_left (by rw [hxm]; exact hr'dvd)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (by rw [← hxm, h, mul_zero]) hx
    · exact h
  have hr'le : r' ≤ m := Nat.le_of_dvd hmpos hr'm
  calc 2 ^ k * rad x ≤ 2 ^ K * (2 * r') :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hkK) (rad_le_two_mul_odd_part x)
    _ = 2 * (2 ^ K * r') := by ring
    _ ≤ 2 * (2 ^ K * m) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hr'le)
    _ = 2 * x := by rw [hxm]

/-- `2 ^ (n + 3) ∣ 3 ^ (2 ^ (n + 1)) - 1`. -/
lemma two_pow_dvd_three_pow (n : ℕ) : 2 ^ (n + 3) ∣ 3 ^ (2 ^ (n + 1)) - 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      obtain ⟨v, hv⟩ := ih
      have hA : (3 : ℕ) ^ (2 ^ (n + 2)) = (3 ^ (2 ^ (n + 1))) ^ 2 := by
        rw [← pow_mul]
        ring_nf
      have hone : 1 ≤ (3 : ℕ) ^ (2 ^ (n + 1)) := Nat.one_le_pow _ _ (by norm_num)
      obtain ⟨t, ht⟩ : ∃ t, (3 : ℕ) ^ (2 ^ (n + 1)) = t + 1 :=
        ⟨3 ^ (2 ^ (n + 1)) - 1, by omega⟩
      have htv : t = 2 ^ (n + 3) * v := by omega
      refine ⟨v * (2 ^ (n + 2) * v + 1), ?_⟩
      have hexp : (t + 1) ^ 2 = t ^ 2 + 2 * t + 1 := by ring
      rw [hA, ht, hexp]
      have : t ^ 2 + 2 * t + 1 - 1 = t ^ 2 + 2 * t := by omega
      rw [this, htv]
      ring

/-! ### The base case `ε = 0`: infinitely many exceptions -/

/-- The witnesses `(1, 3 ^ (2 ^ (n+1)) - 1, 3 ^ (2 ^ (n+1)))`. -/
private def wit (n : ℕ) : ℕ × ℕ × ℕ :=
  (1, 3 ^ (2 ^ (n + 1)) - 1, 3 ^ (2 ^ (n + 1)))

private lemma wit_injective : Function.Injective wit := by
  intro n m h
  have h3 : (3 : ℕ) ^ (2 ^ (n + 1)) = 3 ^ (2 ^ (m + 1)) := congrArg (fun t => t.2.2) h
  have h2 : (2 : ℕ) ^ (n + 1) = 2 ^ (m + 1) := Nat.pow_right_injective (by norm_num) h3
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

private lemma rad_wit_lt (n : ℕ) :
    rad (3 ^ (2 ^ (n + 1)) - 1) * 3 < 3 ^ (2 ^ (n + 1)) := by
  set N := 2 ^ (n + 1) with hN
  have hN2 : 2 ≤ N := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hN] using this
  have hc9 : 9 ≤ (3 : ℕ) ^ N := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hN2
  set b := 3 ^ N - 1 with hb
  have hbne : b ≠ 0 := by omega
  have hdvd : 2 ^ (n + 3) ∣ b := two_pow_dvd_three_pow n
  have hkey : 2 ^ (n + 3) * rad b ≤ 2 * b := two_pow_mul_rad_le hbne hdvd
  have h8 : (8 : ℕ) ≤ 2 ^ (n + 3) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 * rad b ≤ b := by
    have : 8 * rad b ≤ 2 ^ (n + 3) * rad b := Nat.mul_le_mul_right _ h8
    omega
  omega

private lemma wit_mem (n : ℕ) : wit n ∈ AbcExceptions 0 := by
  set N := 2 ^ (n + 1) with hN
  have hNne : N ≠ 0 := by positivity
  have hN2 : 2 ≤ N := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hN] using this
  have hc9 : 9 ≤ (3 : ℕ) ^ N := by
    calc (9 : ℕ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hN2
  set b := 3 ^ N - 1 with hb
  have hbne : b ≠ 0 := by omega
  have hcne : (3 : ℕ) ^ N ≠ 0 := by omega
  have hradle : rad (1 * b * (3 ^ N)) ≤ rad b * 3 := by
    have h1 : (1 : ℕ) * b * 3 ^ N = b * 3 ^ N := by ring
    rw [h1]
    calc rad (b * 3 ^ N) ≤ rad b * rad (3 ^ N) := rad_mul_le hbne hcne
      _ = rad b * 3 := by rw [rad_prime_pow Nat.prime_three hNne]
  have hlt : rad (1 * b * (3 ^ N)) < 3 ^ N := lt_of_le_of_lt hradle (rad_wit_lt n)
  show (1, b, 3 ^ N) ∈ AbcExceptions 0
  simp only [AbcExceptions, Set.mem_setOf_eq]
  refine ⟨by norm_num, by omega, by omega, Nat.coprime_one_left b, ?_⟩
  rw [add_zero, Real.rpow_one]
  exact_mod_cast hlt

lemma abc_exceptions_zero_infinite : (AbcExceptions 0).Infinite :=
  Set.infinite_of_injective_forall_mem wit_injective wit_mem

/-! ### Reduction to small `ε` -/

lemma abcExceptions_anti {δ ε : ℝ} (h : δ ≤ ε) : AbcExceptions ε ⊆ AbcExceptions δ := by
  rintro ⟨a, b, c⟩ ⟨ha, hb, habc, hcop, hlt⟩
  refine ⟨ha, hb, habc, hcop, lt_of_le_of_lt ?_ hlt⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_rad) (by linarith)

/-- **The abc conjecture, formalized**, together with two Lean-checked facts about it:

* it suffices to prove it for all small `ε` (reduction), and
* the statement genuinely fails for `ε = 0`: there are infinitely many coprime triples
  `a + b = c` with `rad (a * b * c) < c`. -/
theorem abc_statement :
    (AbcConjecture ↔ ∀ ε : ℝ, 0 < ε → ε < 1 → (AbcExceptions ε).Finite) ∧
      (AbcExceptions 0).Infinite := by
  refine ⟨⟨fun h ε hε _ => h ε hε, fun h ε hε => ?_⟩, abc_exceptions_zero_infinite⟩
  by_cases h1 : ε < 1
  · exact h ε hε h1
  · exact (h (1 / 2) (by norm_num) (by norm_num)).subset
      (abcExceptions_anti (by push_neg at h1; linarith))

end Frontier

