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

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime divisors. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma one_le_rad (n : ℕ) : 1 ≤ rad n := rad_pos n

lemma one_le_rad_real (n : ℕ) : (1 : ℝ) ≤ (rad n : ℝ) := by
  exact_mod_cast one_le_rad n

/-- The set of `abc`-triples exceptional for the exponent `1 + ε`:
positive coprime `a, b` with `a + b = c` and `rad (a*b*c) ^ (1+ε) < c`. -/
def abcExceptions (ε : ℝ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ 0 < t.2.1 ∧ Nat.Coprime t.1 t.2.1 ∧ t.1 + t.2.1 = t.2.2 ∧
      ((rad (t.1 * t.2.1 * t.2.2) : ℝ)) ^ (1 + ε) < (t.2.2 : ℝ)}

/-- **The abc conjecture** (finiteness form): for every `ε > 0` there are only finitely many
triples of positive coprime integers `a, b` with `a + b = c` and `c > rad (a*b*c) ^ (1+ε)`. -/
def ABCConjecture : Prop := ∀ ε : ℝ, 0 < ε → (abcExceptions ε).Finite

/-- **The abc conjecture** (explicit-constant form): for every `ε > 0` there is a constant
`K_ε > 0` such that `c ≤ K_ε * rad (a*b*c) ^ (1+ε)` for all positive coprime `a, b` with
`a + b = c`. -/
def ABCBounded : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b →
    a + b = c → (c : ℝ) ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε)

/-- Key elementary estimate: if `1 ≤ r` and `r ^ (1+ε) < K * r ^ (1+ε/2)` with `ε > 0`,
then `r` is bounded by `exp (2 * log K / ε)`. -/
lemma rad_le_of_lt (ε K r : ℝ) (hε : 0 < ε) (hr : 1 ≤ r)
    (h : r ^ (1 + ε) < K * r ^ (1 + ε / 2)) :
    r ≤ Real.exp (2 * Real.log K / ε) := by
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have hsplit : r ^ (1 + ε) = r ^ (1 + ε / 2) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0]
    ring_nf
  have hpos : (0 : ℝ) < r ^ (1 + ε / 2) := Real.rpow_pos_of_pos hr0 _
  have hK : r ^ (ε / 2) < K := by
    have := hsplit ▸ h
    nlinarith [this]
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hr0 _) hK.le
  have hlog : (ε / 2) * Real.log r < Real.log K := by
    have h1 : Real.log (r ^ (ε / 2)) < Real.log K :=
      Real.log_lt_log (Real.rpow_pos_of_pos hr0 _) hK
    rwa [Real.log_rpow hr0] at h1
  have hlogr : Real.log r < 2 * Real.log K / ε := by
    rw [lt_div_iff₀ hε]
    nlinarith
  calc r = Real.exp (Real.log r) := (Real.exp_log hr0).symm
    _ ≤ Real.exp (2 * Real.log K / ε) := Real.exp_le_exp.2 hlogr.le

theorem abcConjecture_of_abcBounded (h : ABCBounded) : ABCConjecture := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := h (ε / 2) (by positivity)
  -- we may assume `K ≥ 1`
  set K' : ℝ := max K 1 with hK'def
  have hK'1 : (1 : ℝ) ≤ K' := le_max_right _ _
  have hK'0 : (0 : ℝ) < K' := lt_of_lt_of_le zero_lt_one hK'1
  have hK' : ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
      (c : ℝ) ≤ K' * (rad (a * b * c) : ℝ) ^ (1 + ε / 2) := by
    intro a b c ha hb hab hsum
    refine le_trans (hK a b c ha hb hab hsum) ?_
    have : (0 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε / 2) :=
      le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (one_le_rad_real _)) _)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  set M : ℝ := Real.exp (2 * Real.log K' / ε) with hMdef
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ 2 * Real.log K' / ε := by
      have : 0 ≤ Real.log K' := Real.log_nonneg hK'1
      positivity
    simpa using Real.exp_le_exp.2 this
  set B : ℝ := K' * M ^ (1 + ε / 2) with hBdef
  set N : ℕ := ⌈B⌉₊ with hNdef
  have key : ∀ t ∈ abcExceptions ε, t.1 ≤ N ∧ t.2.1 ≤ N ∧ t.2.2 ≤ N := by
    rintro ⟨a, b, c⟩ ⟨ha, hb, hab, hsum, hlt⟩
    simp only at ha hb hab hsum hlt
    set r : ℝ := (rad (a * b * c) : ℝ) with hrdef
    have hr1 : (1 : ℝ) ≤ r := one_le_rad_real _
    have hub : (c : ℝ) ≤ K' * r ^ (1 + ε / 2) := hK' a b c ha hb hab hsum
    have hstep : r ^ (1 + ε) < K' * r ^ (1 + ε / 2) := lt_of_lt_of_le hlt hub
    have hrM : r ≤ M := rad_le_of_lt ε K' r hε hr1 hstep
    have hcB : (c : ℝ) ≤ B := by
      refine le_trans hub ?_
      rw [hBdef]
      have : r ^ (1 + ε / 2) ≤ M ^ (1 + ε / 2) :=
        Real.rpow_le_rpow (by linarith) hrM (by linarith)
      exact mul_le_mul_of_nonneg_left this hK'0.le
    have hcN : c ≤ N := by
      have : (c : ℝ) ≤ (N : ℝ) := le_trans hcB (by rw [hNdef]; exact Nat.le_ceil B)
      exact_mod_cast this
    refine ⟨?_, ?_, hcN⟩
    · dsimp only
      omega
    · dsimp only
      omega
  refine Set.Finite.subset (Finset.finite_toSet
    ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1)) ×ˢ (Finset.range (N + 1)))) ?_
  intro t ht
  obtain ⟨h1, h2, h3⟩ := key t ht
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
  exact ⟨by omega, by omega, by omega⟩

theorem abcBounded_of_abcConjecture (h : ABCConjecture) : ABCBounded := by
  intro ε hε
  have hfin := h ε hε
  set S : Finset (ℕ × ℕ × ℕ) := hfin.toFinset with hSdef
  refine ⟨1 + ∑ t ∈ S, (t.2.2 : ℝ), ?_, ?_⟩
  · have : (0 : ℝ) ≤ ∑ t ∈ S, (t.2.2 : ℝ) :=
      Finset.sum_nonneg fun t _ => by positivity
    linarith
  · intro a b c ha hb hab hsum
    set K : ℝ := 1 + ∑ t ∈ S, (t.2.2 : ℝ) with hKdef
    have hsum0 : (0 : ℝ) ≤ ∑ t ∈ S, (t.2.2 : ℝ) :=
      Finset.sum_nonneg fun t _ => by positivity
    have hK1 : (1 : ℝ) ≤ K := by rw [hKdef]; linarith
    have hrad1 : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := by
      apply Real.one_le_rpow (one_le_rad_real _)
      linarith
    by_cases hmem : (a, b, c) ∈ abcExceptions ε
    · have hcS : (a, b, c) ∈ S := by rw [hSdef]; simpa using hmem
      have : (c : ℝ) ≤ ∑ t ∈ S, (t.2.2 : ℝ) := by
        have := Finset.single_le_sum (f := fun t : ℕ × ℕ × ℕ => (t.2.2 : ℝ))
          (fun t _ => by positivity) hcS
        simpa using this
      have hcK : (c : ℝ) ≤ K := by rw [hKdef]; linarith
      calc (c : ℝ) ≤ K := hcK
        _ = K * 1 := by ring
        _ ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
            exact mul_le_mul_of_nonneg_left hrad1 (by linarith)
    · have hnot : ¬ ((rad (a * b * c) : ℝ) ^ (1 + ε) < (c : ℝ)) := by
        intro hlt
        exact hmem ⟨ha, hb, hab, hsum, by simpa using hlt⟩
      have hle : (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := not_lt.1 hnot
      calc (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := hle
        _ = 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by ring
        _ ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
            apply mul_le_mul_of_nonneg_right hK1
            linarith

/-- **Statement of the abc conjecture, with a Lean-checked reduction.**

The finiteness form of the abc conjecture (`ABCConjecture`: for every `ε > 0` only finitely many
triples of positive coprime `a, b` with `a + b = c` satisfy `rad (a*b*c) ^ (1+ε) < c`) is
equivalent to the explicit-constant form (`ABCBounded`: for every `ε > 0` there is `K_ε > 0`
with `c ≤ K_ε * rad (a*b*c) ^ (1+ε)` for all such triples). -/
theorem abc_statement : ABCConjecture ↔ ABCBounded :=
  ⟨abcBounded_of_abcConjecture, abcConjecture_of_abcBounded⟩

/-! ### The base case `ε = 0` fails unconditionally

The hypothesis `ε > 0` cannot be dropped: there are infinitely many coprime triples with
`a + b = c` and `rad (a*b*c) < c`, given by `1 + (2 ^ (6n) - 1) = 2 ^ (6n)`. -/

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_mul_of_coprime {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (h : Nat.Coprime x y) :
    rad (x * y) = rad x * rad y := by
  unfold rad
  rw [Nat.primeFactors_mul hx hy, Finset.prod_union h.disjoint_primeFactors]

lemma rad_pow_eq (x : ℕ) {k : ℕ} (hk : k ≠ 0) : rad (x ^ k) = rad x := by
  unfold rad
  rw [Nat.primeFactors_pow x hk]

lemma rad_of_prime {p : ℕ} (hp : p.Prime) : rad p = p := by
  unfold rad
  rw [hp.primeFactors]
  simp

lemma rad_three_mul {k : ℕ} (hk : k ≠ 0) (h3 : 3 ∣ k) : rad (3 * k) = rad k := by
  unfold rad
  have h3p : Nat.Prime 3 := by norm_num
  rw [Nat.primeFactors_mul (by norm_num) hk, h3p.primeFactors]
  congr 1
  rw [Finset.union_eq_right, Finset.singleton_subset_iff, Nat.mem_primeFactors]
  exact ⟨h3p, h3, hk⟩

lemma three_mul_rad_le {m : ℕ} (hm : m ≠ 0) (h9 : 9 ∣ m) : 3 * rad m ≤ m := by
  obtain ⟨t, rfl⟩ := h9
  have ht : t ≠ 0 := by rintro rfl; simp at hm
  have h1 : (9 : ℕ) * t = 3 * (3 * t) := by ring
  rw [h1, rad_three_mul (by positivity) ⟨t, rfl⟩]
  have h2 : rad (3 * t) ≤ 3 * t :=
    Nat.le_of_dvd (by positivity) (rad_dvd (3 * t))
  omega

lemma nine_dvd_two_pow_six_mul_sub_one (n : ℕ) : 9 ∣ 2 ^ (6 * n) - 1 := by
  have h63 : 63 ∣ 64 ^ n - 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨k, hk⟩ := ih
      have h1 : 1 ≤ 64 ^ n := Nat.one_le_pow _ _ (by norm_num)
      have h2 : (64 : ℕ) ^ (n + 1) = 64 * 64 ^ n := by ring
      omega
  have h64 : (2 : ℕ) ^ (6 * n) = 64 ^ n := by
    rw [pow_mul]; norm_num
  rw [h64]
  exact dvd_trans (by norm_num) h63

lemma mem_abcExceptions_zero (n : ℕ) :
    ((1 : ℕ), 2 ^ (6 * (n + 1)) - 1, 2 ^ (6 * (n + 1))) ∈ abcExceptions 0 := by
  set c : ℕ := 2 ^ (6 * (n + 1)) with hc
  have hc64 : 64 ≤ c := by
    have : (2 : ℕ) ^ 6 ≤ 2 ^ (6 * (n + 1)) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [hc] using this
  set b : ℕ := c - 1 with hb
  have hb1 : b + 1 = c := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have h9 : 9 ∣ b := by
    rw [hb, hc]; exact nine_dvd_two_pow_six_mul_sub_one (n + 1)
  have hcop : Nat.Coprime b c := by
    rw [← hb1]; simp
  have hradc : rad c = 2 := by
    rw [hc, rad_pow_eq 2 (by omega), rad_of_prime Nat.prime_two]
  have hradbc : rad (1 * b * c) = rad b * 2 := by
    rw [one_mul, rad_mul_of_coprime hb0 hc0 hcop, hradc]
  have hkey : rad b * 2 < c := by
    have := three_mul_rad_le hb0 h9
    omega
  refine ⟨by norm_num, ?_, ?_, ?_, ?_⟩
  · dsimp only
    omega
  · dsimp only
    simp
  · dsimp only
    omega
  simp only
  rw [hradbc]
  rw [show (1 : ℝ) + 0 = 1 by norm_num, Real.rpow_one]
  exact_mod_cast hkey

/-- The exponent `1 + ε` with `ε > 0` is necessary: for `ε = 0` there are infinitely many
coprime triples `a + b = c` with `rad (a*b*c) < c`. -/
theorem abcExceptions_zero_infinite : (abcExceptions 0).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => ((1 : ℕ), 2 ^ (6 * (n + 1)) - 1, 2 ^ (6 * (n + 1))))
  · intro m n hmn
    simp only [Prod.mk.injEq] at hmn
    have h := hmn.2.2
    have : 6 * (m + 1) = 6 * (n + 1) := Nat.pow_right_injective (le_refl 2) h
    omega
  · intro n
    exact mem_abcExceptions_zero n

end Frontier

