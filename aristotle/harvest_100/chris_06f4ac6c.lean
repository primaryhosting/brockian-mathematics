/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Mathlib does not state the `abc` conjecture. The closest existing material is
`UniqueFactorizationMonoid.radical` (`Mathlib/RingTheory/Radical.lean`), a general radical
of an element of a UFM, and the Mason–Stothers theorem
(`Mathlib/NumberTheory/FLT/MasonStothers.lean`), the polynomial analogue of `abc`.
Neither closes the statement below, so the radical for `ℕ` and both formulations of the
conjecture are set up here from scratch.
-/

namespace Frontier

open scoped BigOperators

/-- The radical of a natural number: the product of its distinct prime factors.
By convention `rad 0 = rad 1 = 1`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma one_le_rad (n : ℕ) : 1 ≤ rad n :=
  Finset.one_le_prod' fun _ hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_le_self {n : ℕ} (hn : 0 < n) : rad n ≤ n := Nat.le_of_dvd hn (rad_dvd n)

/-- The radical is multiplicative on coprime arguments. -/
lemma rad_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : Nat.Coprime m n) :
    rad (m * n) = rad m * rad n := by
  classical
  rw [rad, rad, rad, Nat.primeFactors_mul hm hn,
    Finset.prod_union h.disjoint_primeFactors]

lemma rad_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : rad (p ^ k) = p := by
  rw [rad, Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton]

lemma one_le_rad_real (n : ℕ) : (1 : ℝ) ≤ (rad n : ℝ) := by
  exact_mod_cast one_le_rad n

/-- The set of `abc`-triples exceptional for the exponent `1 + ε`: coprime positive
`a`, `b` with `a + b = c` and `rad (a*b*c) ^ (1+ε) < c`. -/
def abcTriples (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
    (rad (t.1 * t.2.1 * t.2.2) : ℝ) ^ (1 + ε) < (t.2.2 : ℝ)}

/-- The `abc` conjecture, finiteness form: for every `ε > 0` there are only finitely many
coprime triples `a + b = c` with `c > rad (a*b*c) ^ (1+ε)`. -/
def ABCFinite : Prop := ∀ ε : ℝ, 0 < ε → (abcTriples ε).Finite

/-- The `abc` conjecture, effective-constant form: for every `ε > 0` there is `K > 0` with
`c ≤ K * rad (a*b*c) ^ (1+ε)` for all coprime triples `a + b = c`. -/
def ABCBounded : Prop := ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
  ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-- From the finiteness form one extracts an effective constant: the finitely many
exceptional triples are absorbed into `K`. -/
lemma abcBounded_of_abcFinite (h : ABCFinite) : ABCBounded := by
  intro ε hε
  obtain hfin := h ε hε
  classical
  set T := hfin.toFinset with hT
  refine ⟨1 + ∑ t ∈ T, (t.2.2 : ℝ), by positivity, ?_⟩
  intro a b c ha hb hab habc
  have hr : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) :=
    Real.one_le_rpow (one_le_rad_real _) (by linarith)
  have hsum : (0 : ℝ) ≤ ∑ t ∈ T, (t.2.2 : ℝ) :=
    Finset.sum_nonneg fun t _ => by positivity
  by_cases hc : (rad (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ)
  · have hmem : ((a, b, c) : ℕ × ℕ × ℕ) ∈ T := by
      simp only [hT, Set.Finite.mem_toFinset, abcTriples, Set.mem_setOf_eq]
      exact ⟨ha, hb, hab, habc, hc⟩
    have h1 : (c : ℝ) ≤ ∑ t ∈ T, (t.2.2 : ℝ) :=
      Finset.single_le_sum (f := fun t : ℕ × ℕ × ℕ => (t.2.2 : ℝ))
        (fun i _ => by positivity) hmem
    calc (c : ℝ) ≤ 1 + ∑ t ∈ T, (t.2.2 : ℝ) := by linarith
      _ ≤ (1 + ∑ t ∈ T, (t.2.2 : ℝ)) * (rad (a * b * c) : ℝ) ^ (1 + ε) :=
          le_mul_of_one_le_right (by linarith) hr
  · push_neg at hc
    calc (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := hc
      _ ≤ (1 + ∑ t ∈ T, (t.2.2 : ℝ)) * (rad (a * b * c) : ℝ) ^ (1 + ε) := by nlinarith

/-- From the effective-constant form one gets finiteness: applying the bound with `ε/2`
forces the radical, hence `c`, to be bounded on the exceptional set for `ε`. -/
lemma abcFinite_of_abcBounded (h : ABCBounded) : ABCFinite := by
  intro ε hε
  obtain ⟨K, hK, hbound⟩ := h (ε / 2) (by linarith)
  set B : ℝ := K ^ (2 / ε) with hB
  have hB0 : 0 < B := Real.rpow_pos_of_pos hK _
  set M : ℝ := K * B ^ (1 + ε / 2) with hM
  have hM0 : 0 ≤ M := by
    have : (0:ℝ) < B ^ (1 + ε / 2) := Real.rpow_pos_of_pos hB0 _
    positivity
  set N : ℕ := ⌈M⌉₊ with hN
  apply Set.Finite.subset ((Set.finite_Iic N).prod
    ((Set.finite_Iic N).prod (Set.finite_Iic N)))
  rintro ⟨a, b, c⟩ ⟨ha, hb, hab, habc, hc⟩
  dsimp only at ha hb hab habc hc
  have hr1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) := one_le_rad_real _
  set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
  have hcb : (c : ℝ) ≤ K * r ^ (1 + ε / 2) := hbound a b c ha hb hab habc
  have hrpow : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add (by linarith)]
    ring_nf
  have hpos : (0 : ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hkey : r ^ (ε / 2) < K := by
    have h1 : r ^ (1 + ε / 2) * r ^ (ε / 2) < K * r ^ (1 + ε / 2) := by
      rw [← hrpow]; exact lt_of_lt_of_le hc hcb
    nlinarith
  have hrB : r ≤ B := by
    by_contra hlt
    push_neg at hlt
    have : B ^ (ε / 2) < r ^ (ε / 2) :=
      Real.rpow_lt_rpow (le_of_lt hB0) hlt (by linarith)
    have hBe : B ^ (ε / 2) = K := by
      rw [hB, ← Real.rpow_mul (le_of_lt hK)]
      rw [show 2 / ε * (ε / 2) = 1 by field_simp]
      simp
    rw [hBe] at this
    linarith
  have hcM : (c : ℝ) ≤ M := by
    have : r ^ (1 + ε / 2) ≤ B ^ (1 + ε / 2) :=
      Real.rpow_le_rpow (by linarith) hrB (by linarith)
    calc (c : ℝ) ≤ K * r ^ (1 + ε / 2) := hcb
      _ ≤ K * B ^ (1 + ε / 2) := by nlinarith
  have hcN : c ≤ N := by
    have : (c : ℝ) ≤ (N : ℝ) := le_trans hcM (Nat.le_ceil M)
    exact_mod_cast this
  have hac : a ≤ c := by omega
  have hbc : b ≤ c := by omega
  exact ⟨le_trans hac hcN, le_trans hbc hcN, hcN⟩

/-- The two standard formulations of the `abc` conjecture are equivalent. -/
theorem abc_statement : ABCFinite ↔ ABCBounded :=
  ⟨abcBounded_of_abcFinite, abcFinite_of_abcBounded⟩

/-!
## The base case `ε = 0` is false

The `ε` in the `abc` conjecture cannot be dropped: there are infinitely many coprime
triples `a + b = c` with `rad (a*b*c) < c`, given by `1 + (3 ^ 2 ^ n - 1) = 3 ^ 2 ^ n`.
-/

/-- If a large power of `2` divides `b`, then the radical of `b` is correspondingly small. -/
lemma rad_mul_two_pow_le {b j : ℕ} (hb : 0 < b) (h : 2 ^ (j + 1) ∣ b) :
    2 ^ j * rad b ≤ b := by
  set v := b.factorization 2 with hv
  have hvj : j + 1 ≤ v := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hb.ne').mp h
  set m := b / 2 ^ v with hm
  have hsplit : 2 ^ v * m = b := Nat.ordProj_mul_ordCompl_eq_self b 2
  have hmpos : 0 < m := Nat.ordCompl_pos 2 hb.ne'
  have hcop : Nat.Coprime (2 ^ v) m :=
    (Nat.coprime_ordCompl Nat.prime_two hb.ne').pow_left _
  have hradb : rad b = 2 * rad m := by
    rw [← hsplit, rad_mul_of_coprime (by positivity) hmpos.ne' hcop,
      rad_prime_pow Nat.prime_two (by omega)]
  have hmle : rad m ≤ m := rad_le_self hmpos
  calc 2 ^ j * rad b = 2 ^ (j + 1) * rad m := by rw [hradb]; ring
    _ ≤ 2 ^ v * m := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hvj) hmle
    _ = b := hsplit

/-- `2 ^ (k + 3)` divides `3 ^ 2 ^ (k + 1) - 1`. -/
lemma two_pow_dvd_three_pow_sub_one (k : ℕ) : 2 ^ (k + 3) ∣ 3 ^ 2 ^ (k + 1) - 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hx : 1 ≤ 3 ^ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
      obtain ⟨y, hy⟩ : ∃ y, 3 ^ 2 ^ (k + 1) = y + 1 := ⟨3 ^ 2 ^ (k + 1) - 1, by omega⟩
      have hsq : 3 ^ 2 ^ (k + 2) = (3 ^ 2 ^ (k + 1)) ^ 2 := by
        rw [← pow_mul, ← pow_succ]
      have hfac : 3 ^ 2 ^ (k + 2) - 1 = (3 ^ 2 ^ (k + 1) - 1) * (3 ^ 2 ^ (k + 1) + 1) := by
        rw [hsq, hy]
        have : (y + 1) ^ 2 = y * y + 2 * y + 1 := by ring
        rw [this]
        have : (y + 1 - 1) * (y + 1 + 1) = y * y + 2 * y := by
          simp only [Nat.add_sub_cancel]
          ring
        omega
      have heven : 2 ∣ 3 ^ 2 ^ (k + 1) + 1 := by
        have hodd : 3 ^ 2 ^ (k + 1) % 2 = 1 := Nat.pow_mod 3 _ 2 ▸ by simp
        omega
      rw [hfac]
      have : 2 ^ (k + 3) * 2 ∣ (3 ^ 2 ^ (k + 1) - 1) * (3 ^ 2 ^ (k + 1) + 1) :=
        mul_dvd_mul ih heven
      simpa [pow_succ] using this

/-- Each triple `1 + (3 ^ 2 ^ (k+1) - 1) = 3 ^ 2 ^ (k+1)` is an exceptional triple for
`ε = 0`. -/
lemma mem_abcTriples_zero (k : ℕ) :
    ((1, 3 ^ 2 ^ (k + 1) - 1, 3 ^ 2 ^ (k + 1)) : ℕ × ℕ × ℕ) ∈ abcTriples 0 := by
  set c : ℕ := 3 ^ 2 ^ (k + 1) with hc
  have hc9 : 9 ≤ c := by
    calc (9 : ℕ) = 3 ^ 2 ^ 1 := by norm_num
      _ ≤ 3 ^ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
  set b : ℕ := c - 1 with hbdef
  have hb : 0 < b := by omega
  have hsum : 1 + b = c := by omega
  have hcop : Nat.Coprime b c := by
    have : c = b + 1 := by omega
    rw [this]
    simp [Nat.Coprime]
  have hdvd : 2 ^ (k + 2 + 1) ∣ b := two_pow_dvd_three_pow_sub_one k
  have hbound : 2 ^ (k + 2) * rad b ≤ b := rad_mul_two_pow_le hb hdvd
  have hfour : (4 : ℕ) ≤ 2 ^ (k + 2) := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 * rad b ≤ b := le_trans (Nat.mul_le_mul_right _ hfour) hbound
  have hradc : rad c = 3 := rad_prime_pow (by norm_num) (by positivity)
  have hradbc : rad (1 * b * c) = rad b * 3 := by
    rw [one_mul, rad_mul_of_coprime hb.ne' (by omega) hcop, hradc]
  have hlt : rad (1 * b * c) < c := by
    have h1 : 1 ≤ rad b := one_le_rad b
    rw [hradbc]; omega
  refine ⟨one_pos, hb, Nat.coprime_one_left b, hsum, ?_⟩
  have : ((rad (1 * b * c) : ℝ)) < (c : ℝ) := by exact_mod_cast hlt
  simpa using this

/-- **The exponent `1 + ε` is necessary**: with `ε = 0` there are infinitely many coprime
triples `a + b = c` with `rad (a*b*c) < c`. -/
theorem abcTriples_zero_infinite : (abcTriples 0).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => ((1, 3 ^ 2 ^ (k + 1) - 1, 3 ^ 2 ^ (k + 1)) : ℕ × ℕ × ℕ))
  · intro k l hkl
    have h : (3 : ℕ) ^ 2 ^ (k + 1) = 3 ^ 2 ^ (l + 1) := congrArg (fun t => t.2.2) hkl
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 2) this
    omega
  · intro k
    exact mem_abcTriples_zero k

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

