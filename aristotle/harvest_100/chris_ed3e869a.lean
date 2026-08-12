/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Real

/-- The radical of a natural number: the product of its distinct prime divisors. -/
def rad (n : ℕ) : ℕ := n.primeFactors.prod id

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos (fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos)

lemma one_le_rad_real (n : ℕ) : (1 : ℝ) ≤ (rad n : ℝ) := by
  exact_mod_cast rad_pos n

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_le (n : ℕ) (hn : 0 < n) : rad n ≤ n := Nat.le_of_dvd hn (rad_dvd n)

lemma rad_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    rad (a * b) = rad a * rad b := by
  rw [rad, rad, rad, Nat.primeFactors_mul ha hb, Finset.prod_union h.disjoint_primeFactors]

lemma rad_pow {k : ℕ} (n : ℕ) (hk : k ≠ 0) : rad (n ^ k) = rad n := by
  rw [rad, rad, Nat.primeFactors_pow n hk]

lemma rad_prime {p : ℕ} (hp : p.Prime) : rad p = p := by
  rw [rad, hp.primeFactors]; simp

/-- If `8 ∣ m` then the radical of `m` is at most `m / 4`. -/
lemma four_mul_rad_le_of_eight_dvd {m : ℕ} (hm : 0 < m) (h8 : 8 ∣ m) : 4 * rad m ≤ m := by
  obtain ⟨e, t, ht, hmt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' 2 (by norm_num)
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; simp at hmt; omega
    · exact h
  have h2t : Nat.Coprime 2 t := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr ht
  have hcop : Nat.Coprime (2 ^ e) t := Nat.Coprime.pow_left _ h2t
  have he : 3 ≤ e := by
    have h1 : (2 : ℕ) ^ 3 ∣ 2 ^ e * t := by rw [← hmt]; simpa using h8
    have h2 : (2 : ℕ) ^ 3 ∣ 2 ^ e :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 3 h2t) h1
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  have hrad : rad m = 2 * rad t := by
    rw [hmt, rad_mul_of_coprime hcop (by positivity) htpos.ne', rad_pow 2 (by omega),
      rad_prime (by norm_num)]
  have hrt : rad t ≤ t := rad_le t htpos
  have h8e : (8 : ℕ) ≤ 2 ^ e := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  calc 4 * rad m = 8 * rad t := by rw [hrad]; ring
    _ ≤ 8 * t := Nat.mul_le_mul_left _ hrt
    _ ≤ 2 ^ e * t := Nat.mul_le_mul_right _ h8e
    _ = m := hmt.symm

/-- An abc-triple: positive coprime `a`, `b` with `a + b = c`. -/
structure ABCTriple (a b c : ℕ) : Prop where
  ha : 0 < a
  hb : 0 < b
  hsum : a + b = c
  hcop : Nat.Coprime a b

/-- The set of abc-triples that are exceptional for the exponent `1 + ε`, i.e. those
with `c > rad (a * b * c) ^ (1 + ε)`. -/
def exceptionalSet (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {p | ABCTriple p.1 p.2.1 p.2.2 ∧
        ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) < (p.2.2 : ℝ)}

/-- **The abc conjecture**: for every `ε > 0` there are only finitely many coprime triples
`a + b = c` of positive integers with `c > rad (a * b * c) ^ (1 + ε)`. -/
def ABCConjecture : Prop := ∀ ε : ℝ, 0 < ε → (exceptionalSet ε).Finite

/-- The "effective-constant" form of the abc conjecture: for every `ε > 0` there is a
constant `K` with `c ≤ K * rad (a * b * c) ^ (1 + ε)` for all abc-triples. -/
def ABCBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ, ABCTriple a b c →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

lemma abc_bounded_of_conjecture (h : ABCConjecture) : ABCBounded := by
  intro ε hε
  obtain ⟨S, hS⟩ : ∃ S : Finset (ℕ × ℕ × ℕ), ↑S = exceptionalSet ε :=
    ⟨(h ε hε).toFinset, by simp⟩
  refine ⟨1 + ∑ p ∈ S, (p.2.2 : ℝ) / ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε), ?_⟩
  intro a b c ht
  set R : ℝ := (rad (a * b * c) : ℝ) with hR
  have hR1 : (1 : ℝ) ≤ R := one_le_rad_real _
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hpow : (1 : ℝ) ≤ R ^ (1 + ε) :=
    Real.one_le_rpow hR1 (by linarith)
  have hpowpos : (0 : ℝ) < R ^ (1 + ε) := lt_of_lt_of_le zero_lt_one hpow
  have hnonneg : ∀ p ∈ S, (0 : ℝ) ≤
      (p.2.2 : ℝ) / ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) := by
    intro p _
    positivity
  set K : ℝ := 1 + ∑ p ∈ S, (p.2.2 : ℝ) / ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) with hK
  have hsum_nonneg : (0 : ℝ) ≤ ∑ p ∈ S, (p.2.2 : ℝ) /
      ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) := Finset.sum_nonneg hnonneg
  have hK1 : (1 : ℝ) ≤ K := by simp only [hK]; linarith
  by_cases hex : ((a, b, c) : ℕ × ℕ × ℕ) ∈ exceptionalSet ε
  · have hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ S := by rw [← hS] at hex; exact_mod_cast hex
    have hle : (c : ℝ) / R ^ (1 + ε) ≤
        ∑ p ∈ S, (p.2.2 : ℝ) / ((rad (p.1 * p.2.1 * p.2.2) : ℝ)) ^ (1 + ε) :=
      Finset.single_le_sum hnonneg hmem
    have : (c : ℝ) / R ^ (1 + ε) ≤ K := by simp only [hK]; linarith
    calc (c : ℝ) = ((c : ℝ) / R ^ (1 + ε)) * R ^ (1 + ε) := by
              field_simp
      _ ≤ K * R ^ (1 + ε) := by
              exact mul_le_mul_of_nonneg_right this (le_of_lt hpowpos)
  · have : ¬ (R ^ (1 + ε) < (c : ℝ)) := by
      intro hc
      exact hex ⟨ht, hc⟩
    push_neg at this
    calc (c : ℝ) ≤ R ^ (1 + ε) := this
      _ ≤ K * R ^ (1 + ε) := by nlinarith

lemma abc_conjecture_of_bounded (h : ABCBounded) : ABCConjecture := by
  intro ε hε
  obtain ⟨K, hK⟩ := h (ε / 2) (by linarith)
  -- a uniform bound on `c` for exceptional triples
  have hKpos : (0 : ℝ) < max K 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set K' : ℝ := max K 1 with hK'
  have hK'1 : (1 : ℝ) ≤ K' := le_max_right _ _
  have hK'bound : ∀ a b c : ℕ, ABCTriple a b c →
      (c : ℝ) ≤ K' * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
    intro a b c ht
    refine le_trans (hK a b c ht) ?_
    have hpow : (0 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε / 2) :=
      Real.rpow_nonneg (by positivity) _
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  set M : ℝ := K' * (K' ^ (2 / ε)) ^ (1 + ε / 2) with hM
  have key : ∀ p ∈ exceptionalSet ε, (p.2.2 : ℝ) ≤ M := by
    rintro ⟨a, b, c⟩ ⟨ht, hexc⟩
    simp only at ht hexc
    set R : ℝ := (rad (a * b * c) : ℝ) with hR
    have hR1 : (1 : ℝ) ≤ R := one_le_rad_real _
    have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
    have hsplit : R ^ (1 + ε) = R ^ (1 + ε / 2) * R ^ (ε / 2) := by
      rw [← Real.rpow_add hRpos]; ring_nf
    have hupper : (c : ℝ) ≤ K' * R ^ (1 + ε / 2) := hK'bound a b c ht
    have hhalfpos : (0 : ℝ) < R ^ (1 + ε / 2) := Real.rpow_pos_of_pos hRpos _
    have hlt : R ^ (1 + ε / 2) * R ^ (ε / 2) < K' * R ^ (1 + ε / 2) := by
      rw [← hsplit]; linarith
    have hRe : R ^ (ε / 2) < K' := by
      by_contra hcon
      push_neg at hcon
      nlinarith [hlt, hhalfpos]
    have hRle : R ≤ K' ^ (2 / ε) := by
      have h1 : (R ^ (ε / 2)) ^ (2 / ε) = R := by
        rw [← Real.rpow_mul hRpos.le]
        rw [show (ε / 2) * (2 / ε) = 1 by field_simp]
        exact Real.rpow_one R
      calc R = (R ^ (ε / 2)) ^ (2 / ε) := h1.symm
        _ ≤ K' ^ (2 / ε) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hRpos.le _) hRe.le (by positivity)
    have : R ^ (1 + ε / 2) ≤ (K' ^ (2 / ε)) ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (le_of_lt hRpos) hRle (by linarith)
    calc (c : ℝ) ≤ K' * R ^ (1 + ε / 2) := hupper
      _ ≤ K' * (K' ^ (2 / ε)) ^ (1 + ε / 2) := by
          exact mul_le_mul_of_nonneg_left this (le_of_lt hKpos)
  -- hence the exceptional set is contained in a finite box
  obtain ⟨N, hN⟩ := exists_nat_gt M
  have hsub : exceptionalSet ε ⊆ Set.Iic N ×ˢ (Set.Iic N ×ˢ Set.Iic N) := by
    rintro ⟨a, b, c⟩ hp
    have hc : (c : ℝ) ≤ M := key _ hp
    have hcN : c ≤ N := by
      have : (c : ℝ) < (N : ℝ) := lt_of_le_of_lt hc hN
      exact_mod_cast le_of_lt this
    obtain ⟨ht, -⟩ := hp
    have hsum := ht.hsum
    have hb := ht.hb
    have ha := ht.ha
    dsimp only at hsum hb ha
    exact ⟨show a ≤ N by omega, show b ≤ N by omega, show c ≤ N by omega⟩
  exact Set.Finite.subset ((Set.finite_Iic N).prod ((Set.finite_Iic N).prod
    (Set.finite_Iic N))) hsub

/-- **A Lean-checked reduction for the abc conjecture.**
The finiteness form of the abc conjecture (for every `ε > 0` only finitely many coprime
triples `a + b = c` satisfy `c > rad (a * b * c) ^ (1 + ε)`) is equivalent to its
effective-constant form (for every `ε > 0` there is `K` with
`c ≤ K * rad (a * b * c) ^ (1 + ε)` for all coprime triples `a + b = c`). -/
theorem abc_statement : ABCConjecture ↔ ABCBounded :=
  ⟨abc_bounded_of_conjecture, abc_conjecture_of_bounded⟩

/-- The base case `1 + 8 = 9`: this triple already violates the inequality
`c ≤ rad (a * b * c)`, so the exponent `1 + ε` (with `ε > 0`) cannot be replaced by `1`. -/
theorem abc_base_case : ((1, 8, 9) : ℕ × ℕ × ℕ) ∈ exceptionalSet 0 := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  have hrad : rad (1 * 8 * 9) = 6 := by
    have h : (1 * 8 * 9 : ℕ) = 2 ^ 3 * 3 ^ 2 := by norm_num
    rw [rad, h, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow _ (by norm_num), Nat.primeFactors_pow _ (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    decide
  simp only [hrad]
  norm_num

/-- The triples `1 + (9 ^ n - 1) = 9 ^ n` (for `n ≥ 1`) are all exceptional at `ε = 0`:
since `8 ∣ 9 ^ n - 1`, one has `rad (a * b * c) ≤ 3 * (9 ^ n - 1) / 4 < 9 ^ n = c`. -/
lemma nine_pow_triple_mem_exceptional {n : ℕ} (hn : 1 ≤ n) :
    ((1, 9 ^ n - 1, 9 ^ n) : ℕ × ℕ × ℕ) ∈ exceptionalSet 0 := by
  have h9 : 9 ≤ 9 ^ n := by
    calc (9 : ℕ) = 9 ^ 1 := by norm_num
      _ ≤ 9 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set m := 9 ^ n - 1 with hm
  have hmc : m + 1 = 9 ^ n := by omega
  have hmpos : 0 < m := by omega
  have h8 : 8 ∣ m := by
    have h := Nat.sub_dvd_pow_sub_pow 9 1 n
    simpa [hm] using h
  have hkey : 4 * rad m ≤ m := four_mul_rad_le_of_eight_dvd hmpos h8
  have hcop : Nat.Coprime m (9 ^ n) := by
    rw [← hmc]
    simp [Nat.Coprime]
  have hrad9 : rad (9 ^ n) = 3 := by
    have h : (9 : ℕ) ^ n = 3 ^ (2 * n) := by rw [pow_mul]; norm_num
    rw [h, rad_pow 3 (by omega), rad_prime (by norm_num)]
  have hradprod : rad (1 * m * 9 ^ n) = rad m * 3 := by
    rw [one_mul, rad_mul_of_coprime hcop hmpos.ne' (by positivity), hrad9]
  refine ⟨⟨one_pos, hmpos, show 1 + m = 9 ^ n by omega, by simp⟩, ?_⟩
  have hlt : rad m * 3 < 9 ^ n := by omega
  simp only [hradprod, add_zero, Real.rpow_one]
  exact_mod_cast hlt

/-- The exponent `ε > 0` in the abc conjecture cannot be dropped: there are infinitely many
coprime triples `a + b = c` with `c > rad (a * b * c)`. -/
theorem abc_exceptional_zero_infinite : (exceptionalSet 0).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => ((1, 9 ^ (k + 1) - 1, 9 ^ (k + 1)) : ℕ × ℕ × ℕ))
  · intro i j hij
    have h : (9 : ℕ) ^ (i + 1) = 9 ^ (j + 1) := congrArg (fun p => p.2.2) hij
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 9) h
    omega
  · intro k
    exact nine_pow_triple_mem_exceptional (Nat.le_add_left 1 k)

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

